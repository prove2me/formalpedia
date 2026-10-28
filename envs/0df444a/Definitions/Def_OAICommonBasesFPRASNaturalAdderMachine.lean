-- Prove2me | Definitions.Def_OAICommonBasesFPRASNaturalAdderMachine
-- name    : OAICommonBasesFPRASNaturalAdderMachine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T20:48:50.377143+00:00
-- url     : https://prove2.me/theorems/9c86b571-f0c3-463f-af7d-ba7793733a09
-- title:
--   Call-enabled natural binary adder
-- statement:
--   A fixed call-enabled OAI register program adds two little-endian binary natural-number inputs, returns the sum in a register without halting, clears scratch storage, and has linear bit-operation cost with no oracle calls.
-- source:
--   Lean 4.33.1 refinement of the accepted binary adder using the published machine continuation and binary input decoder.

import Definitions.Def_OAICommonBasesFPRASBinaryStackAdderContinuationV3
import Definitions.Def_CountingMatroidBridgeBinarySampler

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Fixed binary adder on natural inputs

This package supplies a reusable, nonhalting OAI adder subroutine. It accepts
little-endian `Nat.bits` operands, returns the sum in register 6, and records
its linear bit-operation cost without invoking the oracle.
-/

namespace OAI.CommonBasesFPRAS

/-- Load natural operands into the call-enabled binary adder. -/
def naturalAdderConfig (a b : ℕ) : MachineConfig 2 24 where
  registers := fun i =>
    match i.val with
    | 6 => a.bits
    | 7 => b.bits
    | _ => []
  control := ⟨0, by omega⟩
  output := none
  oracleCalls := 0
  bitOperations := 0

/-- The call-enabled adder returns the exact sum and leaves scratch clear. -/
theorem naturalAdderConfig_correct {n : ℕ} (O : IndependenceOracle n)
    (coins : ℕ → Bool) (a b : ℕ) :
    let c := naturalAdderConfig a b
    let out := execution
      (binaryStackAdderWithCall (fun _ => Instruction.halt) ⟨0, by omega⟩)
      O c coins (adderTotalSteps a.bits b.bits + 1)
    out.control = ⟨23, by omega⟩ ∧
    binaryValue (out.registers (adderReg 6)) = a + b ∧
    out.registers (adderReg 7) = [true] ∧
    out.registers (adderReg 8) = [] ∧
    out.output = none ∧ out.oracleCalls = 0 := by
  let c := naturalAdderConfig a b
  let P : Program 2 1 := fun _ => Instruction.halt
  let out := execution (binaryStackAdderWithCall P ⟨0, by omega⟩)
    O c coins (adderTotalSteps a.bits b.bits + 1)
  have h := binaryStackAdderWithCall_correct P ⟨0, by omega⟩ O coins c
    a.bits b.bits (by simp [c, naturalAdderConfig])
    (by simp [c, naturalAdderConfig, adderWideState, adderState])
    (by simp [c, naturalAdderConfig, adderReg])
    (by simp [c, naturalAdderConfig, adderReg])
    (by simp [c, naturalAdderConfig, adderReg])
  rcases h with ⟨hcontrol, hsum, hden, hscratch, _, _, _, _, hout', hcalls, _⟩
  have hvalue : binaryValue (addBitsAux false a.bits b.bits) = a + b := by
    rw [binaryValue_addBitsAux]
    simp [CountingMatroid.Bridge.machineBinaryValue_bits]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [out, P] using hcontrol
  · change binaryValue (out.registers (adderReg 6)) = a + b
    rw [show out.registers (adderReg 6) = addBitsAux false a.bits b.bits by
      simpa [out, P] using hsum]
    exact hvalue
  · simpa [out, P] using hden
  · simpa [out, P] using hscratch
  · simpa [out, P] using hout'
  · simpa [out, c, naturalAdderConfig] using hcalls

/-- The natural-input adder makes no oracle calls and has linear bit cost. -/
theorem naturalAdderConfig_resources {n : ℕ} (O : IndependenceOracle n)
    (coins : ℕ → Bool) (a b : ℕ) :
    let c := naturalAdderConfig a b
    let out := execution
      (binaryStackAdderWithCall (fun _ => Instruction.halt) ⟨0, by omega⟩)
      O c coins (adderTotalSteps a.bits b.bits + 1)
    out.oracleCalls = 0 ∧
    out.bitOperations ≤ 6 * max a.bits.length b.bits.length + 10 := by
  let c := naturalAdderConfig a b
  let P : Program 2 1 := fun _ => Instruction.halt
  have h := binaryStackAdderWithCall_cost_le P ⟨0, by omega⟩ O coins c
    a.bits b.bits (by simp [c, naturalAdderConfig])
    (by simp [c, naturalAdderConfig, adderWideState, adderState])
    (by simp [c, naturalAdderConfig, adderReg])
    (by simp [c, naturalAdderConfig, adderReg])
    (by simp [c, naturalAdderConfig, adderReg])
  have hrun := binaryStackAdderWithCall_correct P ⟨0, by omega⟩ O coins c
    a.bits b.bits (by simp [c, naturalAdderConfig])
    (by simp [c, naturalAdderConfig, adderWideState, adderState])
    (by simp [c, naturalAdderConfig, adderReg])
    (by simp [c, naturalAdderConfig, adderReg])
    (by simp [c, naturalAdderConfig, adderReg])
  rcases hrun with ⟨_, _, _, _, _, _, _, _, _, hcalls, _⟩
  constructor
  · simpa [c, naturalAdderConfig] using hcalls
  · simpa [c, naturalAdderConfig, P] using h

end OAI.CommonBasesFPRAS


