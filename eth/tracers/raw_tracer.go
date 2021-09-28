// Copyright 2017 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

package tracers

import (
	"encoding/json"
	"fmt"
	"math/big"
	"sync/atomic"
	"time"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/ethereum/go-ethereum/core"
	"github.com/ethereum/go-ethereum/core/vm"
)

type CallFrame struct {
	op      vm.OpCode
	from    common.Address
	to      common.Address
	value   *big.Int
	gas     uint64
	gasUsed uint64
	input   []byte
	output  []byte
	err     string
	calls   []CallFrame
	// helper fields
	gasIn   uint64
	gasCost uint64
	outOff  int64
	outLen  int64
}

type BlockContext struct {
	// Before capture
	gasPrice *big.Int
	// Capture start
	op           string
	from         common.Address
	to           common.Address
	input        []byte
	gas          uint64
	value        *big.Int
	block        uint64
	intrinsicGas uint64
	// Capture end
	output  []byte
	time    time.Duration
	gasUsed uint64
	err     string
}

// RawTracer provides an implementation of RawTracer that evaluates a Javascript
// function for each VM execution step.
type RawTracer struct {
	tracerObject int // Stack index of the tracer JavaScript object
	stateObject  int // Stack index of the global state to pull arguments from

	pcValue     *uint   // Swappable pc value wrapped by a log accessor
	gasValue    *uint   // Swappable gas value wrapped by a log accessor
	costValue   *uint   // Swappable cost value wrapped by a log accessor
	depthValue  *uint   // Swappable depth value wrapped by a log accessor
	errorValue  *string // Swappable error value wrapped by a log accessor
	refundValue *uint   // Swappable refund value wrapped by a log accessor

	ctx BlockContext // Transaction context gathered throughout execution
	err error        // Error, if one has occurred

	interrupt uint32 // Atomic flag to signal execution interruption
	reason    error  // Textual reason for the interruption

	callstack []CallFrame
	descended bool
}

// New instantiates a new tracer instance. code specifies a Javascript snippet,
// which must evaluate to an expression returning an object with 'step', 'fault'
// and 'result' functions.
func NewRawTracer(code string, txCtx vm.TxContext) (*RawTracer, error) {
	// Resolve any tracers by name and assemble the tracer object
	// TODO: select handler according to code.
	tracer := &RawTracer{
		pcValue:     new(uint),
		gasValue:    new(uint),
		costValue:   new(uint),
		depthValue:  new(uint),
		refundValue: new(uint),
		// init with a single call
		callstack: []CallFrame{{}},
	}
	tracer.ctx.gasPrice = txCtx.GasPrice

	return tracer, nil
}

// Stop terminates execution of the tracer at the first opportune moment.
func (jst *RawTracer) Stop(err error) {
	jst.reason = err
	atomic.StoreUint32(&jst.interrupt, 1)
}

// CaptureStart implements the RawTracer interface to initialize the tracing operation.
func (jst *RawTracer) CaptureStart(env *vm.EVM, from common.Address, to common.Address, create bool, input []byte, gas uint64, value *big.Int) {
	jst.ctx.op = "CALL"
	if create {
		jst.ctx.op = "CREATE"
	}
	jst.ctx.from = from
	jst.ctx.to = to
	jst.ctx.input = input
	jst.ctx.gas = gas
	jst.ctx.value = value

	// Initialize the context
	jst.ctx.block = env.Context.BlockNumber.Uint64()
	// Compute intrinsic gas
	isHomestead := env.ChainConfig().IsHomestead(env.Context.BlockNumber)
	isIstanbul := env.ChainConfig().IsIstanbul(env.Context.BlockNumber)
	intrinsicGas, err := core.IntrinsicGas(input, nil, jst.ctx.op == "CREATE", isHomestead, isIstanbul)
	if err != nil {
		return
	}
	jst.ctx.intrinsicGas = intrinsicGas
}

// CaptureState implements the RawTracer interface to trace a single step of VM execution.
func (rt *RawTracer) CaptureState(env *vm.EVM, pc uint64, op vm.OpCode, gas, cost uint64, scope *vm.ScopeContext, rData []byte, depth int, err error) {
	if rt.err != nil {
		return
	}
	// If tracing was interrupted, set the error and stop
	if atomic.LoadUint32(&rt.interrupt) > 0 {
		rt.err = rt.reason
		return
	}

	*rt.pcValue = uint(pc)
	*rt.gasValue = uint(gas)
	*rt.costValue = uint(cost)
	*rt.depthValue = uint(depth)
	*rt.refundValue = uint(env.StateDB.GetRefund())

	rt.errorValue = nil
	if err != nil {
		rt.errorValue = new(string)
		*rt.errorValue = err.Error()
	}

	if rt.errorValue != nil {
		rt.HandleFault()
		return
	}

	switch op {
	// If a new contract is being created, add to the call stack
	case vm.CREATE, vm.CREATE2:
		// FIXME: originally uses "peek(number)". Not sure if it corresponds to "Back"
		inOff := int64(scope.Stack.Back(1).Uint64())
		inEnd := inOff + int64(scope.Stack.Back(2).Uint64())
		call := CallFrame{
			op:      op,
			from:    scope.Contract.Address(),
			input:   scope.Memory.GetCopy(inOff, inEnd-inOff),
			gasIn:   uint64(*rt.gasValue),
			gasCost: uint64(*rt.costValue),
			value:   scope.Stack.Back(0).ToBig(),
		}
		rt.descended = true
		rt.callstack = append(rt.callstack, call)
		return
	// If a contract is being self destructed, gather that as a subcall too
	case vm.SELFDESTRUCT:
		last_call := &rt.callstack[len(rt.callstack)-1]
		last_call.calls = append(last_call.calls, CallFrame{
			op:      op,
			from:    scope.Contract.Address(),
			to:      common.BigToAddress(scope.Stack.Back(0).ToBig()),
			gasIn:   uint64(*rt.gasValue),
			gasCost: uint64(*rt.costValue),
			value:   env.StateDB.GetBalance(scope.Contract.Address()),
		})
		return
	// If a new method invocation is being done, add to the call stack
	case vm.CALL, vm.CALLCODE, vm.DELEGATECALL, vm.STATICCALL:
		// Skip any pre-compile invocations, those are just fancy opcodes
		to := common.BigToAddress(scope.Stack.Back(1).ToBig())
		_, ok := vm.PrecompiledContractsIstanbul[to]
		if ok {
			return
		}
		var off int
		if op == vm.DELEGATECALL || op == vm.STATICCALL {
			off = 0
		} else {
			off = 1
		}

		inOff := int64(scope.Stack.Back(2 + off).Uint64())
		inEnd := inOff + int64(scope.Stack.Back(3+off).Uint64())

		// Assemble the internal call report and store for completion
		call := CallFrame{
			op:      op,
			from:    scope.Contract.Address(),
			to:      to,
			input:   scope.Memory.GetCopy(inOff, inEnd-inOff),
			gasIn:   uint64(*rt.gasValue),
			gasCost: uint64(*rt.costValue),
			outOff:  int64(scope.Stack.Back(4 + off).Uint64()),
			outLen:  int64(scope.Stack.Back(5 + off).Uint64()),
		}
		if op != vm.DELEGATECALL && op != vm.STATICCALL {
			call.value = scope.Stack.Back(2).ToBig()
		}
		rt.callstack = append(rt.callstack, call)
		rt.descended = true
		return
	}

	// If we've just descended into an inner call, retrieve it's true allowance. We
	// need to extract if from within the call as there may be funky gas dynamics
	// with regard to requested and actually given gas (2300 stipend, 63/64 rule).
	if rt.descended {
		if int(*rt.depthValue) >= len(rt.callstack) {
			rt.callstack[len(rt.callstack)-1].gas = uint64(*rt.gasValue)
		} else {
			// TODO(karalabe): The call was made to a plain account. We currently don't
			// have access to the true gas amount inside the call and so any amount will
			// mostly be wrong since it depends on a lot of input args. Skip gas for now.
		}
		rt.descended = false
	}
	// If an existing call is returning, pop off the call stack
	if op == vm.REVERT {
		rt.callstack[len(rt.callstack)-1].err = "execution reverted"
		return
	}
	if int(*rt.depthValue) == len(rt.callstack)-1 {
		// Pop off the last call and get the execution results
		call := rt.callstack[len(rt.callstack)-1]
		rt.callstack = rt.callstack[:len(rt.callstack)-1]

		if call.op == vm.CREATE || call.op == vm.CREATE2 {
			// If the call was a CREATE, retrieve the contract address and output code
			call.gasUsed = call.gasIn - call.gasCost - uint64(*rt.gasValue)
			// delete call.gasIn; delete call.gasCost;
			call.gasIn = 0
			call.gasCost = 0
			if len(scope.Stack.Data()) > 0 {
				ret := scope.Stack.Back(0).ToBig()
				addr := common.BigToAddress(ret)
				call.to = addr
				call.output = env.StateDB.GetCode(addr)
			} else if call.err == "" {
				call.err = "internal failure" // TODO(karalabe): surface these faults somehow
			}
		} else {
			// If the call was a contract call, retrieve the gas usage and output
			if call.gas > 0 {
				call.gasUsed = call.gasIn - call.gasCost + call.gas - uint64(*rt.gasValue)
			}
			if len(scope.Stack.Data()) > 0 {
				call.output = scope.Memory.GetCopy(call.outOff, call.outLen)
			} else if call.err == "" {
				call.err = "internal failure" // TODO(karalabe): surface these faults somehow
			}
			// delete call.gasIn; delete call.gasCost;
			// delete call.outOff; delete call.outLen
			call.gasIn = 0
			call.gasCost = 0
			call.outOff = 0
			call.outLen = 0
		}
		// Inject the call into the previous one
		last_call := &rt.callstack[len(rt.callstack)-1]
		last_call.calls = append(last_call.calls, call)
	}
}

func (rt *RawTracer) HandleFault() {
	// If the topmost call already reverted, don't handle the additional fault again
	if rt.callstack[len(rt.callstack)-1].err != "" {
		return
	}
	// Pop off the just failed call
	call := rt.callstack[len(rt.callstack)-1]
	rt.callstack = rt.callstack[:len(rt.callstack)-1]
	call.err = *rt.errorValue

	// Consume all available gas and clean any leftovers
	if call.gas > 0 {
		call.gasUsed = call.gas
	}
	// delete call.gasIn; delete call.gasCost;
	// delete call.outOff; delete call.outLen;
	call.gasIn = 0
	call.gasCost = 0
	call.outOff = 0
	call.outLen = 0

	// Flatten the failed call into its parent
	left := len(rt.callstack)
	if left > 0 {
		last_call := &rt.callstack[left-1]
		last_call.calls = append(last_call.calls, call)
		return
	}
	// Last call failed too, leave it in the stack
	rt.callstack = append(rt.callstack, call)
}

// CaptureFault implements the RawTracer interface to trace an execution fault
func (rt *RawTracer) CaptureFault(env *vm.EVM, pc uint64, op vm.OpCode, gas, cost uint64, scope *vm.ScopeContext, depth int, err error) {
	if rt.err != nil {
		return
	}
	// Apart from the error, everything matches the previous invocation
	rt.errorValue = new(string)
	*rt.errorValue = err.Error()
	rt.HandleFault()
	// rt.err = wrapError("fault", err) // This is for JaveScript errors
}

// CaptureEnd is called after the call finishes to finalize the tracing.
func (rt *RawTracer) CaptureEnd(output []byte, gasUsed uint64, t time.Duration, err error) {
	rt.ctx.output = output
	rt.ctx.time = t
	rt.ctx.gasUsed = gasUsed

	if err != nil {
		rt.ctx.err = err.Error()
	}
}

type CallFrameSerializable struct {
	Type    string                  `json:"type"`              // vm.OpCode
	From    string                  `json:"from,omitempty"`    // Address
	To      string                  `json:"to,omitempty"`      // Address
	Value   string                  `json:"value,omitempty"`   // bigInt
	Gas     string                  `json:"gas,omitempty"`     // uint64
	GasUsed string                  `json:"gasUsed,omitempty"` // uint64
	Input   string                  `json:"input,omitempty"`   // []bytes
	Output  string                  `json:"output,omitempty"`  // []bytes
	Error   string                  `json:"error,omitempty"`
	Time    string                  `json:"time,omitempty"` // time.Duration
	Calls   []CallFrameSerializable `json:"calls,omitempty"`
}

func SafeHexEncodeBig(b *big.Int) string {
	if b == nil {
		return ""
	}
	return hexutil.EncodeBig(b)
}

func EncodeUint64(i uint64) string {
	if i == 0 {
		return ""
	}
	return hexutil.EncodeUint64(i)
}

func FinalizeCalls(cf []CallFrame) []CallFrameSerializable {
	parsed := make([]CallFrameSerializable, len(cf))
	for i, s := range cf {
		parsed[i] = CallFrameSerializable{
			Type:    s.op.String(),
			From:    hexutil.Encode(s.from.Bytes()),
			To:      hexutil.Encode(s.to.Bytes()),
			Value:   SafeHexEncodeBig(s.value),
			Gas:     EncodeUint64(s.gas),
			GasUsed: EncodeUint64(s.gasUsed),
			Input:   hexutil.Encode(s.input),
			Output:  hexutil.Encode(s.output),
			Error:   s.err,
			Calls:   FinalizeCalls(s.calls),
		}
	}
	return parsed
}

// GetResult calls the Javascript 'result' function and returns its value, or any accumulated error
func (rt *RawTracer) GetResult() (json.RawMessage, error) {
	result := CallFrameSerializable{
		Type:    rt.ctx.op,
		From:    hexutil.Encode(rt.ctx.from.Bytes()),
		To:      hexutil.Encode(rt.ctx.to.Bytes()),
		Value:   SafeHexEncodeBig(rt.ctx.value),
		Gas:     EncodeUint64(rt.ctx.gas),
		GasUsed: EncodeUint64(rt.ctx.gasUsed),
		Input:   hexutil.Encode(rt.ctx.input),
		Output:  hexutil.Encode(rt.ctx.output),
		Time:    fmt.Sprintf("%s", rt.ctx.time),
	}
	if len(rt.callstack) > 0 {
		result.Calls = FinalizeCalls(rt.callstack[0].calls)
		if rt.callstack[0].err != "" {
			result.Error = rt.callstack[0].err
		} else if rt.ctx.err != "" {
			result.Error = rt.ctx.err
		}
	}
	if result.Error != "" && (result.Error != "execution reverted" || result.Output == "0x") {
		result.Output = ""
	}
	text, err := json.Marshal(result)
	if err != nil {
		fmt.Println("error when serializing result:", err)
	}
	// rt.err = wrapError("result", err) // This is for JaveScript errors
	return text, rt.err
}
