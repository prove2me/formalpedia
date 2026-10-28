-- Prove2me | Definitions.Def_OAICommonBasesFPRASMultiplierContinuation
-- name    : OAICommonBasesFPRASMultiplierContinuation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T21:07:45.333982+00:00
-- url     : https://prove2.me/theorems/743c7b11-e879-48df-b8c7-7eaef1e70f3c
-- title:
--   Multiplier return continuation
-- statement:
--   A fixed binary-stack multiplication program can replace its terminal halt with a return step to a fixed continuation. When the multiplier is at its return boundary and the marker stack is empty, that step preserves the register contents, output, and oracle-call count, and adds one bit operation.
-- source:
--   Lean 4.33.1 continuation wrapper around the published natural binary multiplier machine.

import Definitions.Def_OAICommonBasesFPRASNaturalMultiplierMachineV2

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.CommonBasesFPRAS

/-- Keep the multiplier's original control numbers in the larger program. -/
def liftMultiplierState {s : ℕ} (q : Fin 38) : Fin (s + 39) :=
  ⟨q.val, by have h := q.isLt; omega⟩

/-- Place a continuation after the multiplier's reserved states 0 through 37. -/
def shiftMultiplierState {s : ℕ} (q : Fin (s + 1)) : Fin (s + 39) :=
  ⟨q.val + 38, by have h := q.isLt; omega⟩

def liftMultiplierInstruction {s : ℕ} :
    Instruction 2 37 → Instruction 2 (s + 38)
  | .push i b q => .push i b (liftMultiplierState q)
  | .pop i empty zero one =>
      .pop i (liftMultiplierState empty) (liftMultiplierState zero)
        (liftMultiplierState one)
  | .coin zero one =>
      .coin (liftMultiplierState zero) (liftMultiplierState one)
  | .query which i no yes =>
      .query which i (liftMultiplierState no) (liftMultiplierState yes)
  | .halt => .halt

def shiftMultiplierInstruction {s : ℕ} :
    Instruction 2 s → Instruction 2 (s + 38)
  | .push i b q => .push i b (shiftMultiplierState q)
  | .pop i empty zero one =>
      .pop i (shiftMultiplierState empty) (shiftMultiplierState zero)
        (shiftMultiplierState one)
  | .coin zero one =>
      .coin (shiftMultiplierState zero) (shiftMultiplierState one)
  | .query which i no yes =>
      .query which i (shiftMultiplierState no) (shiftMultiplierState yes)
  | .halt => .halt

/-- Run the verified multiplier, replace its final halt with a one-step return,
and place any fixed continuation at offset 38. State 37 remains the original
invalid-input halt branch. -/
def binaryStackMultiplierWithCall {s : ℕ} (P : Program 2 s) :
    Program 2 (s + 38) := fun q =>
  if h : q.val < 36 then
    liftMultiplierInstruction (binaryStackMultiplierProgram ⟨q.val, by omega⟩)
  else if q.val = 36 then
    .pop (adderReg 3) ⟨38, by omega⟩ ⟨38, by omega⟩ ⟨38, by omega⟩
  else if q.val = 37 then
    .halt
  else
    shiftMultiplierInstruction (P ⟨q.val - 38, by have hq := q.isLt; omega⟩)

theorem binaryStackMultiplierWithCall_multiplier_state {s : ℕ}
    (P : Program 2 s) (q : Fin (s + 39)) (hq : q.val < 36) :
    binaryStackMultiplierWithCall P q =
      liftMultiplierInstruction (binaryStackMultiplierProgram ⟨q.val, by omega⟩) := by
  simp [binaryStackMultiplierWithCall, hq]

theorem binaryStackMultiplierWithCall_return_state {s : ℕ}
    (P : Program 2 s) (q : Fin (s + 39)) (hq : 38 ≤ q.val) :
    binaryStackMultiplierWithCall P q =
      shiftMultiplierInstruction (P ⟨q.val - 38, by omega⟩) := by
  simp [binaryStackMultiplierWithCall, show ¬ q.val < 36 by omega,
    show q.val ≠ 36 by omega, show q.val ≠ 37 by omega]

/-- A completed multiplier state with an empty call marker returns to the
continuation without changing any register, output, or oracle count. -/
theorem binaryStackMultiplierWithCall_return_step {s n : ℕ}
    (P : Program 2 s) (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 (s + 38))
    (hcontrol : c.control = ⟨36, by omega⟩)
    (hout : c.output = none) (hmarker : c.registers (adderReg 3) = []) :
    let out := execution (binaryStackMultiplierWithCall P) O c bits 1
    out.control = ⟨38, by omega⟩ ∧ out.registers = c.registers ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 1 := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  simp only at hcontrol hout hmarker
  subst control
  subst output
  simp [adderReg] at hmarker
  simp [execution, machineStep, binaryStackMultiplierWithCall,
    adderReg, hmarker]

end OAI.CommonBasesFPRAS


