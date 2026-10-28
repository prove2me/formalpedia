-- Prove2me | Definitions.Def_OAICommonBasesFPRASBinaryStackAdderContinuationV3
-- name    : OAICommonBasesFPRASBinaryStackAdderContinuationV3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T20:38:52.619291+00:00
-- url     : https://prove2.me/theorems/87ca3ec5-7a00-4905-9711-28af7309b7a8
-- title:
--   Composable binary adder and shift-and-add multiplier
-- statement:
--   A fixed OAI register program embeds the verified binary adder behind a return trampoline and uses it to implement a shift-and-add binary multiplier. The module proves the complete machine trace, exact output, and a quadratic bit-operation bound.
-- source:
--   Lean 4.33.1 binary-register implementation verified locally; source definitions and proofs are included in the published module.

import Theorems.Thm_OAI_CommonBasesFPRAS_binaryStackAdder_correct
import Definitions.Def_OAICommonBasesFPRASBinaryStackArithmeticSupportV2

set_option autoImplicit false

/-!
# Composable binary adder for the estimator machine

The published adder ends by executing `halt`, which is unsuitable for use as
an estimator subroutine. This file embeds its proved instruction block into a
larger fixed program, replaces the halt with a return trampoline, and proves
the complete addition trace and exact cost through that continuation.
-/

namespace OAI.CommonBasesFPRAS

private theorem embedded_addBitsPass_length (carry : Bool) (a b : List Bool) :
    (addBitsPass carry a b).1.length = max a.length b.length := by
  induction a generalizing b carry with
  | nil =>
      induction b generalizing carry with
      | nil => simp [addBitsPass]
      | cons b bs ih =>
          cases carry <;> cases b <;> simp [addBitsPass, addColumn, ih]
  | cons a as ih =>
      cases b with
      | nil => cases carry <;> cases a <;> simp [addBitsPass, addColumn, ih]
      | cons b bs =>
          cases carry <;> cases a <;> cases b <;>
            simp [addBitsPass, addColumn, ih, Order.succ_max, Nat.succ_eq_add_one]

private theorem embedded_adderFinalScratch_length_le (a b : List Bool) :
    (adderFinalScratch a b).length ≤ max a.length b.length + 1 := by
  simp only [adderFinalScratch]
  split <;> simp [List.length_reverse, embedded_addBitsPass_length]

private theorem embedded_addBitsAux_length_le (carry : Bool) (a b : List Bool) :
    (addBitsAux carry a b).length ≤ max a.length b.length + 1 := by
  rw [addBitsAux_eq_addBitsPass]
  simp only [List.length_append, List.length_singleton]
  rw [embedded_addBitsPass_length]
  cases (addBitsPass carry a b).2 <;> simp <;> omega

/-- Lift an adder instruction into the larger control alphabet while keeping
its targets at the original adder states. -/
def liftAdderInstruction {s : ℕ} :
    Instruction 2 21 → Instruction 2 (s + 23)
  | .push i b q => .push i b ⟨q.val, by have hq := q.isLt; omega⟩
  | .pop i empty zero one =>
      .pop i ⟨empty.val, by have hq := empty.isLt; omega⟩
        ⟨zero.val, by have hq := zero.isLt; omega⟩
        ⟨one.val, by have hq := one.isLt; omega⟩
  | .coin zero one =>
      .coin ⟨zero.val, by have hq := zero.isLt; omega⟩
        ⟨one.val, by have hq := one.isLt; omega⟩
  | .query which i no yes =>
      .query which i ⟨no.val, by have hq := no.isLt; omega⟩
        ⟨yes.val, by have hq := yes.isLt; omega⟩
  | .halt => .halt

/-- Embed a numeric adder state into the enlarged control alphabet. -/
def adderWideState {s : ℕ} (q : Fin 22) : Fin (s + 24) :=
  ⟨q.val, by have hq := q.isLt; omega⟩

/-- Shift the control targets of a continuation by the 23 reserved adder and
return states. -/
def shiftAdderContinuationInstruction {s : ℕ} :
    Instruction 2 s → Instruction 2 (s + 23)
  | .push i b q => .push i b ⟨q.val + 23, by have hq := q.isLt; omega⟩
  | .pop i empty zero one =>
      .pop i ⟨empty.val + 23, by have hq := empty.isLt; omega⟩
        ⟨zero.val + 23, by have hq := zero.isLt; omega⟩
        ⟨one.val + 23, by have hq := one.isLt; omega⟩
  | .coin zero one =>
      .coin ⟨zero.val + 23, by have hq := zero.isLt; omega⟩
        ⟨one.val + 23, by have hq := one.isLt; omega⟩
  | .query which i no yes =>
      .query which i ⟨no.val + 23, by have hq := no.isLt; omega⟩
        ⟨yes.val + 23, by have hq := yes.isLt; omega⟩
  | .halt => .halt

/-- The proved adder prefix, followed by a two-instruction return trampoline
and an arbitrary continuation beginning at state 23. -/
def binaryStackAdderThenProgram {s : ℕ} (P : Program 2 s) : Program 2 (s + 23) :=
  fun q =>
    if h : q.val < 21 then
      let sourceState : Fin 22 := ⟨q.val, by omega⟩
      liftAdderInstruction (s := s) (binaryStackAdder sourceState)
    else if q.val = 21 then
      .push ⟨9, by omega⟩ false ⟨22, by omega⟩
    else if q.val = 22 then
      .pop ⟨9, by omega⟩ ⟨23, by omega⟩ ⟨23, by omega⟩ ⟨23, by omega⟩
    else
      let continuationState : Fin (s + 1) := ⟨q.val - 23, by have hq := q.isLt; omega⟩
      shiftAdderContinuationInstruction (P continuationState)

/-- Below the old halt state, the enlarged program is exactly the old adder
instruction with only its control alphabet widened. -/
theorem binaryStackAdderThenProgram_adder_state
    {s : ℕ} (P : Program 2 s) (q : Fin (s + 24)) (hq : q.val < 21) :
    binaryStackAdderThenProgram P q =
      liftAdderInstruction (binaryStackAdder ⟨q.val, by omega⟩) := by
  simp [binaryStackAdderThenProgram, hq]

/-- Every continuation instruction is placed at offset 23. -/
theorem binaryStackAdderThenProgram_continuation_state
    {s : ℕ} (P : Program 2 s) (q : Fin (s + 24)) (hq : 23 ≤ q.val) :
    binaryStackAdderThenProgram P q =
      shiftAdderContinuationInstruction
        (P ⟨q.val - 23, by omega⟩) := by
  simp [binaryStackAdderThenProgram, show ¬ q.val < 21 by omega,
    show q.val ≠ 21 by omega, show q.val ≠ 22 by omega]

/-- Reverse the adder's scratch stack and reach its terminal state before
executing the original halt instruction. Registers 6 and 7 hold the sum and
the denominator-one marker; register 8 is cleared. -/
theorem binaryStackAdder_reverse_before_halt
    (O : IndependenceOracle 0) (bits : ℕ → Bool)
    (c : MachineConfig 2 21) (acc stack : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = adderState 16)
    (hnum : c.registers (adderReg 6) = acc)
    (hden : c.registers (adderReg 7) = [])
    (hscratch : c.registers (adderReg 8) = stack) :
    let out := execution binaryStackAdder O c bits (2 * stack.length + 2)
    out.control = adderState 21 ∧
    out.registers (adderReg 6) = stack.reverse ++ acc ∧
    out.registers (adderReg 7) = [true] ∧
    out.registers (adderReg 8) = [] ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 2 * stack.length + 2 := by
  induction stack generalizing acc c bits with
  | nil =>
      rcases c with ⟨regs, control, output, calls, ops⟩
      simp only at hout hcontrol hnum hden hscratch
      subst control
      subst output
      simp [adderReg] at hnum hden hscratch
      simp [execution, machineStep, binaryStackAdder, adderState, adderReg,
        hnum, hden, hscratch, Function.update]
  | cons bit rest ih =>
      simp only [List.length_cons] at *
      have hstep := binaryStackAdder_reverseColumn O bits c bit acc rest
        hout hcontrol hnum hden hscratch
      rcases hstep with ⟨hctl, hnum', hden', hscratch', hout', hcalls', hcost'⟩
      let c' := execution binaryStackAdder O c bits 2
      have htail := ih (acc := bit :: acc) (c := c')
        (bits := fun t => bits (2 + t)) hout' hctl hnum' hden' hscratch'
      rw [show 2 * (rest.length + 1) + 2 = 2 + (2 * rest.length + 2) by omega,
        execution_append]
      simp_all [List.reverse_cons, List.append_assoc, Nat.add_assoc, c'] <;> omega

/-- One two-step reversal iteration inside the enlarged program agrees with
the original adder's reversal step. -/
theorem binaryStackAdderThenProgram_reverseColumn
    {s n : ℕ} (P : Program 2 s) (O : IndependenceOracle n)
    (bits : ℕ → Bool) (c : MachineConfig 2 (s + 23)) (bit : Bool)
    (acc rest : List Bool) (hout : c.output = none)
    (hcontrol : c.control = ⟨16, by omega⟩)
    (hnum : c.registers (adderReg 6) = acc)
    (hden : c.registers (adderReg 7) = [])
    (hscratch : c.registers (adderReg 8) = bit :: rest) :
    let out := execution (binaryStackAdderThenProgram P) O c bits 2
    out.control = ⟨16, by omega⟩ ∧ out.registers (adderReg 6) = bit :: acc ∧
    out.registers (adderReg 7) = [] ∧ out.registers (adderReg 8) = rest ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 2 := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  simp only at hout hcontrol hnum hden hscratch
  subst control
  subst output
  simp [adderReg] at hnum hden hscratch
  cases bit <;>
    simp [execution, machineStep, binaryStackAdderThenProgram,
      liftAdderInstruction, binaryStackAdder, adderWideState, adderState, adderReg,
      hnum, hden, hscratch, Function.update]

/-- The embedded adder reaches its return boundary after reversing any
temporary result. This is the arithmetic trace needed to call it as a
subroutine; the return trampoline is a separate two-step theorem below. -/
theorem binaryStackAdderThenProgram_reverse_before_return
    {s n : ℕ} (P : Program 2 s) (O : IndependenceOracle n)
    (bits : ℕ → Bool) (c : MachineConfig 2 (s + 23)) (acc stack : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = ⟨16, by omega⟩)
    (hnum : c.registers (adderReg 6) = acc)
    (hden : c.registers (adderReg 7) = [])
    (hscratch : c.registers (adderReg 8) = stack) :
    let out := execution (binaryStackAdderThenProgram P) O c bits
      (2 * stack.length + 2)
    out.control = ⟨21, by omega⟩ ∧
    out.registers (adderReg 6) = stack.reverse ++ acc ∧
    out.registers (adderReg 7) = [true] ∧
    out.registers (adderReg 8) = [] ∧ out.output = none ∧
    out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 2 * stack.length + 2 := by
  induction stack generalizing acc c bits with
  | nil =>
      rcases c with ⟨regs, control, output, calls, ops⟩
      simp only at hout hcontrol hnum hden hscratch
      subst control
      subst output
      simp [adderReg] at hnum hden hscratch
      simp [execution, machineStep, binaryStackAdderThenProgram,
        liftAdderInstruction, binaryStackAdder, adderState, adderReg,
        hnum, hden, hscratch, Function.update]
  | cons bit rest ih =>
      simp only [List.length_cons] at *
      have hstep := binaryStackAdderThenProgram_reverseColumn P O bits c bit acc rest
        hout hcontrol hnum hden hscratch
      rcases hstep with ⟨hctl, hnum', hden', hscratch', hout', hcalls', hcost'⟩
      let c' := execution (binaryStackAdderThenProgram P) O c bits 2
      have htail := ih (acc := bit :: acc) (c := c')
        (bits := fun t => bits (2 + t)) hout' hctl hnum' hden' hscratch'
      rw [show 2 * (rest.length + 1) + 2 = 2 + (2 * rest.length + 2) by omega,
        execution_append]
      simp_all [List.reverse_cons, List.append_assoc, Nat.add_assoc, c'] <;> omega

/-- The adder's halt state is replaced by a two-step trampoline. It reaches the
estimator continuation at state 23, leaving all registers, output, and
oracle-call count unchanged. -/
theorem binaryStackAdderThenProgram_return
    {s n : ℕ} (P : Program 2 s) (O : IndependenceOracle n)
    (bits : ℕ → Bool) (c : MachineConfig 2 (s + 23))
    (hout : c.output = none)
    (hcontrol : c.control = ⟨21, by omega⟩) :
    let out := execution (binaryStackAdderThenProgram P) O c bits 2
    out.control = ⟨23, by omega⟩ ∧
    out.registers = c.registers ∧ out.output = none ∧
    out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 2 := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  simp only at hout hcontrol
  subst control
  subst output
  simp [execution, machineStep, binaryStackAdderThenProgram, Function.update]

/-- Process one pair of input bits inside the embedded adder. -/
theorem binaryStackAdderThenProgram_column
    {s n : ℕ} (P : Program 2 s) (O : IndependenceOracle n)
    (bits : ℕ → Bool) (c : MachineConfig 2 (s + 23))
    (carry a b : Bool) (as bs : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = adderWideState (adderState (if carry then 4 else 0)))
    (hleft : c.registers (adderReg 6) = a :: as)
    (hright : c.registers (adderReg 7) = b :: bs) :
    let out := execution (binaryStackAdderThenProgram P) O c bits 3
    out.control = adderWideState (adderState (if (addColumn a b carry).2 then 4 else 0)) ∧
    out.registers (adderReg 6) = as ∧ out.registers (adderReg 7) = bs ∧
    out.registers (adderReg 8) = (addColumn a b carry).1 :: c.registers (adderReg 8) ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 3 := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  simp only at hout hcontrol hleft hright
  subst control
  subst output
  simp [adderReg] at hleft hright
  cases carry <;> cases a <;> cases b <;>
    simp [execution, machineStep, binaryStackAdderThenProgram,
      liftAdderInstruction, binaryStackAdder, adderWideState, adderState, adderReg,
      addColumn, hleft, hright, Function.update]

/-- The embedded adder also handles a remaining left bit after the right
input is exhausted. -/
theorem binaryStackAdderThenProgram_column_rightEmpty
    {s n : ℕ} (P : Program 2 s) (O : IndependenceOracle n)
    (bits : ℕ → Bool) (c : MachineConfig 2 (s + 23))
    (carry a : Bool) (as : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = adderWideState (adderState (if carry then 4 else 0)))
    (hleft : c.registers (adderReg 6) = a :: as)
    (hright : c.registers (adderReg 7) = []) :
    let out := execution (binaryStackAdderThenProgram P) O c bits 3
    out.control = adderWideState (adderState (if (addColumn a false carry).2 then 4 else 0)) ∧
    out.registers (adderReg 6) = as ∧ out.registers (adderReg 7) = [] ∧
    out.registers (adderReg 8) = (addColumn a false carry).1 :: c.registers (adderReg 8) ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 3 := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  simp only at hout hcontrol hleft hright
  subst control
  subst output
  simp [adderReg] at hleft hright
  cases carry <;> cases a <;>
    simp [execution, machineStep, binaryStackAdderThenProgram,
      liftAdderInstruction, binaryStackAdder, adderWideState, adderState, adderReg,
      addColumn, hleft, hright, Function.update]

/-- The embedded adder handles a remaining right bit after the left input is
exhausted. -/
theorem binaryStackAdderThenProgram_column_leftEmpty
    {s n : ℕ} (P : Program 2 s) (O : IndependenceOracle n)
    (bits : ℕ → Bool) (c : MachineConfig 2 (s + 23))
    (carry b : Bool) (bs : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = adderWideState (adderState (if carry then 4 else 0)))
    (hleft : c.registers (adderReg 6) = [])
    (hright : c.registers (adderReg 7) = b :: bs) :
    let out := execution (binaryStackAdderThenProgram P) O c bits 3
    out.control = adderWideState (adderState (if (addColumn false b carry).2 then 4 else 0)) ∧
    out.registers (adderReg 6) = [] ∧ out.registers (adderReg 7) = bs ∧
    out.registers (adderReg 8) = (addColumn false b carry).1 :: c.registers (adderReg 8) ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 3 := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  simp only at hout hcontrol hleft hright
  subst control
  subst output
  simp [adderReg] at hleft hright
  cases carry <;> cases b <;>
    simp [execution, machineStep, binaryStackAdderThenProgram,
      liftAdderInstruction, binaryStackAdder, adderWideState, adderState, adderReg,
      addColumn, hleft, hright, Function.update]

/-- The carry-completion path is unchanged in the embedded adder. -/
theorem binaryStackAdderThenProgram_finishCarry
    {s n : ℕ} (P : Program 2 s) (O : IndependenceOracle n)
    (bits : ℕ → Bool) (c : MachineConfig 2 (s + 23))
    (carry : Bool) (scratch : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = adderWideState (adderState (if carry then 4 else 0)))
    (hleft : c.registers (adderReg 6) = [])
    (hright : c.registers (adderReg 7) = [])
    (hscratch : c.registers (adderReg 8) = scratch) :
    let steps := if carry then 3 else 2
    let out := execution (binaryStackAdderThenProgram P) O c bits steps
    out.control = ⟨16, by omega⟩ ∧ out.registers (adderReg 6) = [] ∧
    out.registers (adderReg 7) = [] ∧
    out.registers (adderReg 8) = (if carry then true :: scratch else scratch) ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + steps := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  simp only at hout hcontrol hleft hright hscratch
  subst control
  subst output
  simp [adderReg] at hleft hright hscratch
  cases carry <;>
    simp [execution, machineStep, binaryStackAdderThenProgram,
      liftAdderInstruction, binaryStackAdder, adderWideState, adderState, adderReg,
      hleft, hright, hscratch, Function.update]

/-- The enlarged program performs the same three-step column loop as the
proved adder, including either input being exhausted. -/
theorem binaryStackAdderThenProgram_computeLoop
    {s n : ℕ} (P : Program 2 s) (O : IndependenceOracle n)
    (bits : ℕ → Bool) (c : MachineConfig 2 (s + 23)) (carry : Bool)
    (a b scratch : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = adderWideState (adderState (if carry then 4 else 0)))
    (hleft : c.registers (adderReg 6) = a)
    (hright : c.registers (adderReg 7) = b)
    (hscratch : c.registers (adderReg 8) = scratch) :
    let out := execution (binaryStackAdderThenProgram P) O c bits
      (3 * max a.length b.length)
    out.control = adderWideState (adderState (if (addBitsPass carry a b).2 then 4 else 0)) ∧
    out.registers (adderReg 6) = [] ∧ out.registers (adderReg 7) = [] ∧
    out.registers (adderReg 8) = (addBitsPass carry a b).1.reverse ++ scratch ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 3 * max a.length b.length := by
  induction a generalizing b carry c scratch bits with
  | nil =>
      induction b generalizing carry c scratch bits with
      | nil =>
          simp [execution, addBitsPass, hout, hcontrol, hleft, hright, hscratch,
            adderWideState, adderState]
      | cons b bs ih =>
          simp only [List.length_cons, List.length_nil] at *
          have hstep := binaryStackAdderThenProgram_column_leftEmpty P O bits c carry b bs
            hout hcontrol hleft hright
          rcases hstep with ⟨hctl, h6, h7, h8, hout', hcalls, hcost⟩
          let c' := execution (binaryStackAdderThenProgram P) O c bits 3
          have h8' : c'.registers (adderReg 8) = (addColumn false b carry).1 :: scratch := by
            simpa [c'] using h8.trans (by simpa using hscratch)
          have hlen : 3 * max 0 (bs.length + 1) = 3 + 3 * max 0 bs.length := by
            simp [Nat.max_def] <;> omega
          rw [hlen, execution_append]
          have htail := ih (carry := (addColumn false b carry).2) (c := c')
            (scratch := (addColumn false b carry).1 :: scratch)
            (bits := fun t => bits (3 + t)) hout' hctl h6 h7 h8'
          simp_all [addBitsPass, addColumn, adderWideState, adderState,
            List.reverse_cons, List.append_assoc, Nat.add_assoc, c'] <;> rfl
  | cons a as ih =>
      cases b with
      | nil =>
          simp only [List.length_cons, List.length_nil] at *
          have hstep := binaryStackAdderThenProgram_column_rightEmpty P O bits c carry a as
            hout hcontrol hleft hright
          rcases hstep with ⟨hctl, h6, h7, h8, hout', hcalls, hcost⟩
          let c' := execution (binaryStackAdderThenProgram P) O c bits 3
          have h8' : c'.registers (adderReg 8) = (addColumn a false carry).1 :: scratch := by
            simpa [c'] using h8.trans (by simpa using hscratch)
          have hlen : 3 * max (as.length + 1) 0 = 3 + 3 * max as.length 0 := by
            simp [Nat.max_def] <;> omega
          rw [hlen, execution_append]
          have htail := ih (b := []) (carry := (addColumn a false carry).2) (c := c')
            (scratch := (addColumn a false carry).1 :: scratch)
            (bits := fun t => bits (3 + t)) hout' hctl h6 h7 h8'
          simp_all [addBitsPass, addColumn, adderWideState, adderState,
            List.reverse_cons, List.append_assoc, Nat.add_assoc, c'] <;> rfl
      | cons b bs =>
          simp only [List.length_cons, List.length_nil] at *
          have hstep := binaryStackAdderThenProgram_column P O bits c carry a b as bs
            hout hcontrol hleft hright
          rcases hstep with ⟨hctl, h6, h7, h8, hout', hcalls, hcost⟩
          let c' := execution (binaryStackAdderThenProgram P) O c bits 3
          have h8' : c'.registers (adderReg 8) = (addColumn a b carry).1 :: scratch := by
            simpa [c'] using h8.trans (by simpa using hscratch)
          have hlen : 3 * max (as.length + 1) (bs.length + 1) =
              3 + 3 * max as.length bs.length := by
            have hmax : max (as.length + 1) (bs.length + 1) =
                max as.length bs.length + 1 := by
              simpa [Nat.succ_eq_add_one] using
                (Order.succ_max as.length bs.length).symm
            rw [hmax]
            omega
          rw [hlen, execution_append]
          have htail := ih (b := bs) (carry := (addColumn a b carry).2) (c := c')
            (scratch := (addColumn a b carry).1 :: scratch)
            (bits := fun t => bits (3 + t)) hout' hctl h6 h7 h8'
          simp_all [addBitsPass, addColumn, adderWideState, adderState,
            List.reverse_cons, List.append_assoc, Nat.add_assoc, c'] <;> rfl

/-- Complete the proved adder inside a larger fixed program. The combined
machine returns to continuation state 23 instead of halting, with the exact
binary sum in register 6 and the denominator marker in register 7. -/
theorem binaryStackAdderThenProgram_correct
    {s n : ℕ} (P : Program 2 s) (O : IndependenceOracle n)
    (bits : ℕ → Bool) (c : MachineConfig 2 (s + 23)) (a b : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = adderWideState (adderState 0))
    (hleft : c.registers (adderReg 6) = a)
    (hright : c.registers (adderReg 7) = b)
    (hscratch : c.registers (adderReg 8) = []) :
    let out := execution (binaryStackAdderThenProgram P) O c bits
      (adderTotalSteps a b + 1)
    out.control = ⟨23, by omega⟩ ∧
    out.registers (adderReg 6) = (addBitsAux false a b) ∧
    out.registers (adderReg 7) = [true] ∧
    out.registers (adderReg 8) = [] ∧ out.output = none ∧
    out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 3 * max a.length b.length +
      adderCarrySteps a b + 2 * (adderFinalScratch a b).length + 4 := by
  let firstSteps := 3 * max a.length b.length
  let carrySteps := adderCarrySteps a b
  let scratch := adderFinalScratch a b
  let reverseSteps := 2 * scratch.length + 2
  let pass := addBitsPass false a b
  have hloop := binaryStackAdderThenProgram_computeLoop P O bits c false a b []
    hout hcontrol hleft hright hscratch
  rcases hloop with ⟨hctl₁, h6₁, h7₁, h8₁, hout₁, hcalls₁, hcost₁⟩
  let c₁ := execution (binaryStackAdderThenProgram P) O c bits firstSteps
  have h8₁' : c₁.registers (adderReg 8) = pass.1.reverse := by
    simpa [c₁, firstSteps, pass] using h8₁
  have hcarry := binaryStackAdderThenProgram_finishCarry P O
    (fun t => bits (firstSteps + t)) c₁ pass.2 pass.1.reverse
    hout₁ hctl₁ h6₁ h7₁ h8₁'
  rcases hcarry with ⟨hctl₂, h6₂, h7₂, h8₂, hout₂, hcalls₂, hcost₂⟩
  let c₂ := execution (binaryStackAdderThenProgram P) O c₁
    (fun t => bits (firstSteps + t)) carrySteps
  have hrev := binaryStackAdderThenProgram_reverse_before_return P O
    (fun t => bits (firstSteps + carrySteps + t)) c₂ [] scratch
    hout₂ hctl₂ h6₂ h7₂ h8₂
  rcases hrev with ⟨hctl₃, h6₃, h7₃, h8₃, hout₃, hcalls₃, hcost₃⟩
  have hsum : scratch.reverse = addBitsAux false a b := by
    dsimp [scratch, adderFinalScratch, pass]
    rw [addBitsAux_eq_addBitsPass]
    cases hcarryBit : (addBitsPass false a b).2 <;>
      simp [hcarryBit, List.reverse_cons, List.reverse_reverse]
  let c₃ := execution (binaryStackAdderThenProgram P) O c₂
    (fun t => bits (firstSteps + carrySteps + t)) reverseSteps
  let c₄ := execution (binaryStackAdderThenProgram P) O c₃
    (fun t => bits (firstSteps + carrySteps + reverseSteps + t)) 2
  have hreturn := binaryStackAdderThenProgram_return P O
    (fun t => bits (firstSteps + carrySteps + reverseSteps + t)) c₃ hout₃ hctl₃
  have hfinal : c₄.control = ⟨23, by omega⟩ ∧ c₄.registers (adderReg 6) = addBitsAux false a b ∧
      c₄.registers (adderReg 7) = [true] ∧ c₄.registers (adderReg 8) = [] ∧
      c₄.output = none ∧ c₄.oracleCalls = c.oracleCalls ∧
      c₄.bitOperations = c.bitOperations + firstSteps + carrySteps + reverseSteps + 2 := by
    rcases hreturn with ⟨hrctl, hrregs, hrout, hrcalls, hrcost⟩
    have hcalls₁' : c₁.oracleCalls = c.oracleCalls := by
      simpa [c₁, firstSteps] using hcalls₁
    have hcalls₂' : c₂.oracleCalls = c₁.oracleCalls := by
      simpa [c₂, carrySteps, pass, adderCarrySteps] using hcalls₂
    have hcost₁' : c₁.bitOperations = c.bitOperations + firstSteps := by
      simpa [c₁, firstSteps] using hcost₁
    have hcost₂' : c₂.bitOperations = c₁.bitOperations + carrySteps := by
      simpa [c₂, carrySteps, pass, adderCarrySteps] using hcost₂
    constructor
    · exact hrctl
    constructor
    · rw [hrregs]
      simpa [c₃, reverseSteps, hsum] using h6₃
    constructor
    · rw [hrregs]
      simpa [c₃, reverseSteps] using h7₃
    constructor
    · rw [hrregs]
      simpa [c₃, reverseSteps] using h8₃
    constructor
    · exact hrout
    constructor
    · calc
        c₄.oracleCalls = c₃.oracleCalls := hrcalls
        _ = c₂.oracleCalls := hcalls₃
        _ = c₁.oracleCalls := hcalls₂'
        _ = c.oracleCalls := hcalls₁'
    · calc
        c₄.bitOperations = c₃.bitOperations + 2 := by
          simpa [c₄, c₃] using hrcost
        _ = c₂.bitOperations + reverseSteps + 2 := by
          have h : c₃.bitOperations = c₂.bitOperations + reverseSteps := by
            simpa [c₃, reverseSteps, Nat.add_assoc] using hcost₃
          rw [h]
        _ = c.bitOperations + firstSteps + carrySteps + reverseSteps + 2 := by
          rw [hcost₂', hcost₁']
  have hcompose := execution_append_three (binaryStackAdderThenProgram P) O c bits
    firstSteps carrySteps (reverseSteps + 2)
  have hsplit := execution_append (binaryStackAdderThenProgram P) O c₂
    (fun t => bits (firstSteps + carrySteps + t)) reverseSteps 2
  have htotal : adderTotalSteps a b + 1 = firstSteps + (carrySteps + (reverseSteps + 2)) := by
    dsimp [adderTotalSteps, adderCarrySteps, firstSteps, carrySteps,
      reverseSteps, scratch, adderFinalScratch]
    omega
  have hrun : execution (binaryStackAdderThenProgram P) O c bits
        (adderTotalSteps a b + 1) = c₄ := by
    rw [htotal, hcompose, hsplit]
    have htape :
        (fun t => bits (firstSteps + carrySteps + (reverseSteps + t))) =
          (fun t => bits (firstSteps + carrySteps + reverseSteps + t)) := by
      funext t
      congr 1
      omega
    simpa [c₂, c₃, c₄, firstSteps, carrySteps, reverseSteps, htape]
  rcases hfinal with ⟨hctl, h6, h7, h8, hout', hcalls, hcost⟩
  constructor
  · change (execution (binaryStackAdderThenProgram P) O c bits
      (adderTotalSteps a b + 1)).control = _
    rw [hrun]
    exact hctl
  constructor
  · change (execution (binaryStackAdderThenProgram P) O c bits
      (adderTotalSteps a b + 1)).registers (adderReg 6) = _
    rw [hrun]
    exact h6
  constructor
  · change (execution (binaryStackAdderThenProgram P) O c bits
      (adderTotalSteps a b + 1)).registers (adderReg 7) = _
    rw [hrun]
    exact h7
  constructor
  · change (execution (binaryStackAdderThenProgram P) O c bits
      (adderTotalSteps a b + 1)).registers (adderReg 8) = _
    rw [hrun]
    exact h8
  constructor
  · change (execution (binaryStackAdderThenProgram P) O c bits
      (adderTotalSteps a b + 1)).output = none
    rw [hrun]
    exact hout'
  constructor
  · change (execution (binaryStackAdderThenProgram P) O c bits
      (adderTotalSteps a b + 1)).oracleCalls = _
    rw [hrun]
    exact hcalls
  · change (execution (binaryStackAdderThenProgram P) O c bits
      (adderTotalSteps a b + 1)).bitOperations = _
    rw [hrun]
    simpa [firstSteps, reverseSteps, Nat.add_assoc] using hcost

/-- The embedded addition subroutine uses at most a linear number of bit
operations in its input width. -/
theorem binaryStackAdderThenProgram_cost_le
    {s n : ℕ} (P : Program 2 s) (O : IndependenceOracle n)
    (bits : ℕ → Bool) (c : MachineConfig 2 (s + 23)) (a b : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = adderWideState (adderState 0))
    (hleft : c.registers (adderReg 6) = a)
    (hright : c.registers (adderReg 7) = b)
    (hscratch : c.registers (adderReg 8) = []) :
    (execution (binaryStackAdderThenProgram P) O c bits
      (adderTotalSteps a b + 1)).bitOperations ≤
      c.bitOperations + 6 * max a.length b.length + 10 := by
  rcases binaryStackAdderThenProgram_correct P O bits c a b hout hcontrol
    hleft hright hscratch with ⟨_, _, _, _, _, _, hcost⟩
  have hcarry : adderCarrySteps a b ≤ 3 := by
    by_cases h : (addBitsPass false a b).2 <;> simp [adderCarrySteps, h]
  have hscratchLen := embedded_adderFinalScratch_length_le a b
  rw [hcost]
  omega

/-- Map a continuation control target to the adder entry when it is the
designated call site; all other targets stay in the continuation block. -/
def adderCallTarget {s : ℕ} (call q : Fin (s + 1)) : Fin (s + 24) :=
  if q = call then ⟨0, by omega⟩ else ⟨q.val + 23, by have hq := q.isLt; omega⟩

/-- Compile continuation instructions with one distinguished target that
loops back to the adder entry. -/
def adderCallInstruction {s : ℕ} (call : Fin (s + 1)) :
    Instruction 2 s → Instruction 2 (s + 23)
  | .push i b q => .push i b (adderCallTarget call q)
  | .pop i empty zero one =>
      .pop i (adderCallTarget call empty) (adderCallTarget call zero)
        (adderCallTarget call one)
  | .coin zero one =>
      .coin (adderCallTarget call zero) (adderCallTarget call one)
  | .query which i no yes =>
      .query which i (adderCallTarget call no) (adderCallTarget call yes)
  | .halt => .halt

/-- The binary adder with a continuation that may call it again by targeting
one designated continuation state. It starts at the adder; each return goes
to continuation state zero, and a target equal to `call` jumps back to adder
state zero. -/
def binaryStackAdderWithCall {s : ℕ} (P : Program 2 s)
    (call : Fin (s + 1)) : Program 2 (s + 23) := fun q =>
  if h : q.val < 21 then
    liftAdderInstruction (binaryStackAdder ⟨q.val, by omega⟩)
  else if q.val = 21 then
    .push ⟨9, by omega⟩ false ⟨22, by omega⟩
  else if q.val = 22 then
    .pop ⟨9, by omega⟩ ⟨23, by omega⟩ ⟨23, by omega⟩ ⟨23, by omega⟩
  else
    adderCallInstruction call (P ⟨q.val - 23, by have hq := q.isLt; omega⟩)

/-- One paired-bit computation is unchanged when continuation targets can
loop back to the adder. -/
theorem binaryStackAdderWithCall_column
    {s n : ℕ} (P : Program 2 s) (call : Fin (s + 1))
    (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 (s + 23)) (carry a b : Bool) (as bs : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = adderWideState (adderState (if carry then 4 else 0)))
    (hleft : c.registers (adderReg 6) = a :: as)
    (hright : c.registers (adderReg 7) = b :: bs) :
    let out := execution (binaryStackAdderWithCall P call) O c bits 3
    out.control = adderWideState (adderState (if (addColumn a b carry).2 then 4 else 0)) ∧
    out.registers (adderReg 6) = as ∧ out.registers (adderReg 7) = bs ∧
    out.registers (adderReg 8) = (addColumn a b carry).1 :: c.registers (adderReg 8) ∧
    out.registers (adderReg 9) = c.registers (adderReg 9) ∧
    out.registers (adderReg 3) = c.registers (adderReg 3) ∧
    out.registers (adderReg 4) = c.registers (adderReg 4) ∧
    out.registers (adderReg 5) = c.registers (adderReg 5) ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 3 := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  simp only at hout hcontrol hleft hright
  subst control
  subst output
  simp [adderReg] at hleft hright
  cases carry <;> cases a <;> cases b <;>
    simp [execution, machineStep, binaryStackAdderWithCall,
      liftAdderInstruction, adderWideState, binaryStackAdder, adderState,
      adderReg, addColumn, hleft, hright, Function.update]

theorem binaryStackAdderWithCall_column_rightEmpty
    {s n : ℕ} (P : Program 2 s) (call : Fin (s + 1))
    (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 (s + 23)) (carry a : Bool) (as : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = adderWideState (adderState (if carry then 4 else 0)))
    (hleft : c.registers (adderReg 6) = a :: as)
    (hright : c.registers (adderReg 7) = []) :
    let out := execution (binaryStackAdderWithCall P call) O c bits 3
    out.control = adderWideState (adderState (if (addColumn a false carry).2 then 4 else 0)) ∧
    out.registers (adderReg 6) = as ∧ out.registers (adderReg 7) = [] ∧
    out.registers (adderReg 8) = (addColumn a false carry).1 :: c.registers (adderReg 8) ∧
    out.registers (adderReg 9) = c.registers (adderReg 9) ∧
    out.registers (adderReg 3) = c.registers (adderReg 3) ∧
    out.registers (adderReg 4) = c.registers (adderReg 4) ∧
    out.registers (adderReg 5) = c.registers (adderReg 5) ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 3 := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  simp only at hout hcontrol hleft hright
  subst control
  subst output
  simp [adderReg] at hleft hright
  cases carry <;> cases a <;>
    simp [execution, machineStep, binaryStackAdderWithCall,
      liftAdderInstruction, adderWideState, binaryStackAdder, adderState,
      adderReg, addColumn, hleft, hright, Function.update]

theorem binaryStackAdderWithCall_column_leftEmpty
    {s n : ℕ} (P : Program 2 s) (call : Fin (s + 1))
    (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 (s + 23)) (carry b : Bool) (bs : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = adderWideState (adderState (if carry then 4 else 0)))
    (hleft : c.registers (adderReg 6) = [])
    (hright : c.registers (adderReg 7) = b :: bs) :
    let out := execution (binaryStackAdderWithCall P call) O c bits 3
    out.control = adderWideState (adderState (if (addColumn false b carry).2 then 4 else 0)) ∧
    out.registers (adderReg 6) = [] ∧ out.registers (adderReg 7) = bs ∧
    out.registers (adderReg 8) = (addColumn false b carry).1 :: c.registers (adderReg 8) ∧
    out.registers (adderReg 9) = c.registers (adderReg 9) ∧
    out.registers (adderReg 3) = c.registers (adderReg 3) ∧
    out.registers (adderReg 4) = c.registers (adderReg 4) ∧
    out.registers (adderReg 5) = c.registers (adderReg 5) ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 3 := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  simp only at hout hcontrol hleft hright
  subst control
  subst output
  simp [adderReg] at hleft hright
  cases carry <;> cases b <;>
    simp [execution, machineStep, binaryStackAdderWithCall,
      liftAdderInstruction, adderWideState, binaryStackAdder, adderState,
      adderReg, addColumn, hleft, hright, Function.update]

theorem binaryStackAdderWithCall_finishCarry
    {s n : ℕ} (P : Program 2 s) (call : Fin (s + 1))
    (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 (s + 23)) (carry : Bool) (scratch : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = adderWideState (adderState (if carry then 4 else 0)))
    (hleft : c.registers (adderReg 6) = [])
    (hright : c.registers (adderReg 7) = [])
    (hscratch : c.registers (adderReg 8) = scratch) :
    let steps := if carry then 3 else 2
    let out := execution (binaryStackAdderWithCall P call) O c bits steps
    out.control = ⟨16, by omega⟩ ∧ out.registers (adderReg 6) = [] ∧
    out.registers (adderReg 7) = [] ∧
    out.registers (adderReg 8) = (if carry then true :: scratch else scratch) ∧
    out.registers (adderReg 9) = c.registers (adderReg 9) ∧
    out.registers (adderReg 3) = c.registers (adderReg 3) ∧
    out.registers (adderReg 4) = c.registers (adderReg 4) ∧
    out.registers (adderReg 5) = c.registers (adderReg 5) ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + steps := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  simp only at hout hcontrol hleft hright hscratch
  subst control
  subst output
  simp [adderReg] at hleft hright hscratch
  cases carry <;>
    simp [execution, machineStep, binaryStackAdderWithCall,
      liftAdderInstruction, adderWideState, binaryStackAdder, adderState,
      adderReg, hleft, hright, hscratch, Function.update]

theorem binaryStackAdderWithCall_reverseColumn
    {s n : ℕ} (P : Program 2 s) (call : Fin (s + 1))
    (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 (s + 23)) (bit : Bool) (acc rest : List Bool)
    (hout : c.output = none) (hcontrol : c.control = ⟨16, by omega⟩)
    (hnum : c.registers (adderReg 6) = acc)
    (hden : c.registers (adderReg 7) = [])
    (hscratch : c.registers (adderReg 8) = bit :: rest) :
    let out := execution (binaryStackAdderWithCall P call) O c bits 2
    out.control = ⟨16, by omega⟩ ∧ out.registers (adderReg 6) = bit :: acc ∧
    out.registers (adderReg 7) = [] ∧ out.registers (adderReg 8) = rest ∧
    out.registers (adderReg 9) = c.registers (adderReg 9) ∧
    out.registers (adderReg 3) = c.registers (adderReg 3) ∧
    out.registers (adderReg 4) = c.registers (adderReg 4) ∧
    out.registers (adderReg 5) = c.registers (adderReg 5) ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 2 := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  simp only at hout hcontrol hnum hden hscratch
  subst control
  subst output
  simp [adderReg] at hnum hden hscratch
  cases bit <;>
    simp [execution, machineStep, binaryStackAdderWithCall,
      liftAdderInstruction, binaryStackAdder, adderState, adderReg,
      hnum, hden, hscratch, Function.update]

theorem binaryStackAdderWithCall_reverse_before_return
    {s n : ℕ} (P : Program 2 s) (call : Fin (s + 1))
    (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 (s + 23)) (acc stack : List Bool)
    (hout : c.output = none) (hcontrol : c.control = ⟨16, by omega⟩)
    (hnum : c.registers (adderReg 6) = acc)
    (hden : c.registers (adderReg 7) = [])
    (hscratch : c.registers (adderReg 8) = stack) :
    let out := execution (binaryStackAdderWithCall P call) O c bits
      (2 * stack.length + 2)
    out.control = ⟨21, by omega⟩ ∧
    out.registers (adderReg 6) = stack.reverse ++ acc ∧
    out.registers (adderReg 7) = [true] ∧
    out.registers (adderReg 8) = [] ∧
    out.registers (adderReg 9) = c.registers (adderReg 9) ∧
    out.registers (adderReg 3) = c.registers (adderReg 3) ∧
    out.registers (adderReg 4) = c.registers (adderReg 4) ∧
    out.registers (adderReg 5) = c.registers (adderReg 5) ∧ out.output = none ∧
    out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 2 * stack.length + 2 := by
  induction stack generalizing acc c bits with
  | nil =>
      rcases c with ⟨regs, control, output, calls, ops⟩
      simp only at hout hcontrol hnum hden hscratch
      subst control
      subst output
      simp [adderReg] at hnum hden hscratch
      simp [execution, machineStep, binaryStackAdderWithCall,
        liftAdderInstruction, binaryStackAdder, adderState, adderReg,
        hnum, hden, hscratch, Function.update]
  | cons bit rest ih =>
      simp only [List.length_cons] at *
      have hstep := binaryStackAdderWithCall_reverseColumn P call O bits c bit acc rest
        hout hcontrol hnum hden hscratch
      rcases hstep with ⟨hctl, hnum', hden', hscratch', hreg9', hreg3', hreg4', hreg5', hout', hcalls', hcost'⟩
      let c' := execution (binaryStackAdderWithCall P call) O c bits 2
      have htail := ih (acc := bit :: acc) (c := c')
        (bits := fun t => bits (2 + t)) hout' hctl hnum' hden' hscratch'
      rw [show 2 * (rest.length + 1) + 2 = 2 + (2 * rest.length + 2) by omega,
        execution_append]
      simp_all [List.reverse_cons, List.append_assoc, Nat.add_assoc, c'] <;> omega

theorem binaryStackAdderWithCall_computeLoop
    {s n : ℕ} (P : Program 2 s) (call : Fin (s + 1))
    (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 (s + 23)) (carry : Bool)
    (a b scratch : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = adderWideState (adderState (if carry then 4 else 0)))
    (hleft : c.registers (adderReg 6) = a)
    (hright : c.registers (adderReg 7) = b)
    (hscratch : c.registers (adderReg 8) = scratch) :
    let out := execution (binaryStackAdderWithCall P call) O c bits
      (3 * max a.length b.length)
    out.control = adderWideState (adderState (if (addBitsPass carry a b).2 then 4 else 0)) ∧
    out.registers (adderReg 6) = [] ∧ out.registers (adderReg 7) = [] ∧
    out.registers (adderReg 8) = (addBitsPass carry a b).1.reverse ++ scratch ∧
    out.registers (adderReg 9) = c.registers (adderReg 9) ∧
    out.registers (adderReg 3) = c.registers (adderReg 3) ∧
    out.registers (adderReg 4) = c.registers (adderReg 4) ∧
    out.registers (adderReg 5) = c.registers (adderReg 5) ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 3 * max a.length b.length := by
  induction a generalizing b carry c scratch bits with
  | nil =>
      induction b generalizing carry c scratch bits with
      | nil =>
          simp [execution, addBitsPass, hout, hcontrol, hleft, hright, hscratch,
            binaryStackAdderWithCall, adderWideState, adderState]
      | cons b bs ih =>
          simp only [List.length_cons, List.length_nil] at *
          have hstep := binaryStackAdderWithCall_column_leftEmpty P call O bits c carry b bs
            hout hcontrol hleft hright
          rcases hstep with ⟨hctl, h6, h7, h8, hreg9, hreg3, hreg4, hreg5, hout', hcalls, hcost⟩
          let c' := execution (binaryStackAdderWithCall P call) O c bits 3
          have h8' : c'.registers (adderReg 8) = (addColumn false b carry).1 :: scratch := by
            simpa [c'] using h8.trans (by simpa using hscratch)
          have hlen : 3 * max 0 (bs.length + 1) = 3 + 3 * max 0 bs.length := by
            simp [Nat.max_def] <;> omega
          rw [hlen, execution_append]
          have htail := ih (carry := (addColumn false b carry).2) (c := c')
            (scratch := (addColumn false b carry).1 :: scratch)
            (bits := fun t => bits (3 + t)) hout' hctl h6 h7 h8'
          simp_all [addBitsPass, addColumn, binaryStackAdderWithCall,
            adderWideState, adderState, List.reverse_cons, List.append_assoc,
            Nat.add_assoc, c'] <;> rfl
  | cons a as ih =>
      cases b with
      | nil =>
          simp only [List.length_cons, List.length_nil] at *
          have hstep := binaryStackAdderWithCall_column_rightEmpty P call O bits c carry a as
            hout hcontrol hleft hright
          rcases hstep with ⟨hctl, h6, h7, h8, hreg9, hreg3, hreg4, hreg5, hout', hcalls, hcost⟩
          let c' := execution (binaryStackAdderWithCall P call) O c bits 3
          have h8' : c'.registers (adderReg 8) = (addColumn a false carry).1 :: scratch := by
            simpa [c'] using h8.trans (by simpa using hscratch)
          have hlen : 3 * max (as.length + 1) 0 = 3 + 3 * max as.length 0 := by
            simp [Nat.max_def] <;> omega
          rw [hlen, execution_append]
          have htail := ih (b := []) (carry := (addColumn a false carry).2) (c := c')
            (scratch := (addColumn a false carry).1 :: scratch)
            (bits := fun t => bits (3 + t)) hout' hctl h6 h7 h8'
          simp_all [addBitsPass, addColumn, binaryStackAdderWithCall,
            adderWideState, adderState, List.reverse_cons, List.append_assoc,
            Nat.add_assoc, c'] <;> rfl
      | cons b bs =>
          simp only [List.length_cons, List.length_nil] at *
          have hstep := binaryStackAdderWithCall_column P call O bits c carry a b as bs
            hout hcontrol hleft hright
          rcases hstep with ⟨hctl, h6, h7, h8, hreg9, hreg3, hreg4, hreg5, hout', hcalls, hcost⟩
          let c' := execution (binaryStackAdderWithCall P call) O c bits 3
          have h8' : c'.registers (adderReg 8) = (addColumn a b carry).1 :: scratch := by
            simpa [c'] using h8.trans (by simpa using hscratch)
          have hlen : 3 * max (as.length + 1) (bs.length + 1) =
              3 + 3 * max as.length bs.length := by
            have hmax : max (as.length + 1) (bs.length + 1) =
                max as.length bs.length + 1 := by
              simpa [Nat.succ_eq_add_one] using
                (Order.succ_max as.length bs.length).symm
            rw [hmax]
            omega
          rw [hlen, execution_append]
          have htail := ih (b := bs) (carry := (addColumn a b carry).2) (c := c')
            (scratch := (addColumn a b carry).1 :: scratch)
            (bits := fun t => bits (3 + t)) hout' hctl h6 h7 h8'
          simp_all [addBitsPass, addColumn, binaryStackAdderWithCall,
            adderWideState, adderState, List.reverse_cons, List.append_assoc,
            Nat.add_assoc, c'] <;> rfl

theorem binaryStackAdderWithCall_return
    {s n : ℕ} (P : Program 2 s) (call : Fin (s + 1))
    (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 (s + 23)) (hout : c.output = none)
    (hcontrol : c.control = ⟨21, by omega⟩) :
    let out := execution (binaryStackAdderWithCall P call) O c bits 2
    out.control = ⟨23, by omega⟩ ∧ out.registers = c.registers ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 2 := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  simp only at hout hcontrol
  subst control
  subst output
  simp [execution, machineStep, binaryStackAdderWithCall, Function.update]

/-- The entire adder trace remains valid when the continuation's distinguished
call edges jump back to adder state zero. -/
theorem binaryStackAdderWithCall_correct
    {s n : ℕ} (P : Program 2 s) (call : Fin (s + 1))
    (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 (s + 23)) (a b : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = adderWideState (adderState 0))
    (hleft : c.registers (adderReg 6) = a)
    (hright : c.registers (adderReg 7) = b)
    (hscratch : c.registers (adderReg 8) = []) :
    let out := execution (binaryStackAdderWithCall P call) O c bits
      (adderTotalSteps a b + 1)
    out.control = ⟨23, by omega⟩ ∧
    out.registers (adderReg 6) = addBitsAux false a b ∧
    out.registers (adderReg 7) = [true] ∧
    out.registers (adderReg 8) = [] ∧
    out.registers (adderReg 9) = c.registers (adderReg 9) ∧
    out.registers (adderReg 3) = c.registers (adderReg 3) ∧
    out.registers (adderReg 4) = c.registers (adderReg 4) ∧
    out.registers (adderReg 5) = c.registers (adderReg 5) ∧ out.output = none ∧
    out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 3 * max a.length b.length +
      adderCarrySteps a b + 2 * (adderFinalScratch a b).length + 4 := by
  let firstSteps := 3 * max a.length b.length
  let carrySteps := adderCarrySteps a b
  let scratch := adderFinalScratch a b
  let reverseSteps := 2 * scratch.length + 2
  let pass := addBitsPass false a b
  have hloop := binaryStackAdderWithCall_computeLoop P call O bits c false a b []
    hout hcontrol hleft hright hscratch
  rcases hloop with ⟨hctl₁, h6₁, h7₁, h8₁, h9₁, hreg3₁, hreg4₁, hreg5₁, hout₁, hcalls₁, hcost₁⟩
  let c₁ := execution (binaryStackAdderWithCall P call) O c bits firstSteps
  have h8₁' : c₁.registers (adderReg 8) = pass.1.reverse := by
    simpa [c₁, firstSteps, pass] using h8₁
  have hcarry := binaryStackAdderWithCall_finishCarry P call O
    (fun t => bits (firstSteps + t)) c₁ pass.2 pass.1.reverse
    hout₁ hctl₁ h6₁ h7₁ h8₁'
  rcases hcarry with ⟨hctl₂, h6₂, h7₂, h8₂, h9₂, hreg3₂, hreg4₂, hreg5₂, hout₂, hcalls₂, hcost₂⟩
  let c₂ := execution (binaryStackAdderWithCall P call) O c₁
    (fun t => bits (firstSteps + t)) carrySteps
  have hrev := binaryStackAdderWithCall_reverse_before_return P call O
    (fun t => bits (firstSteps + carrySteps + t)) c₂ [] scratch
    hout₂ hctl₂ h6₂ h7₂ h8₂
  rcases hrev with ⟨hctl₃, h6₃, h7₃, h8₃, h9₃, hreg3₃, hreg4₃, hreg5₃, hout₃, hcalls₃, hcost₃⟩
  have hsum : scratch.reverse = addBitsAux false a b := by
    dsimp [scratch, adderFinalScratch, pass]
    rw [addBitsAux_eq_addBitsPass]
    cases hcarryBit : (addBitsPass false a b).2 <;>
      simp [hcarryBit, List.reverse_cons, List.reverse_reverse]
  let c₃ := execution (binaryStackAdderWithCall P call) O c₂
    (fun t => bits (firstSteps + carrySteps + t)) reverseSteps
  let c₄ := execution (binaryStackAdderWithCall P call) O c₃
    (fun t => bits (firstSteps + carrySteps + reverseSteps + t)) 2
  have hreturn := binaryStackAdderWithCall_return P call O
    (fun t => bits (firstSteps + carrySteps + reverseSteps + t)) c₃ hout₃ hctl₃
  have hcalls₁' : c₁.oracleCalls = c.oracleCalls := by
    simpa [c₁, firstSteps] using hcalls₁
  have hcalls₂' : c₂.oracleCalls = c₁.oracleCalls := by
    simpa [c₂, carrySteps, pass, adderCarrySteps] using hcalls₂
  have hcost₁' : c₁.bitOperations = c.bitOperations + firstSteps := by
    simpa [c₁, firstSteps] using hcost₁
  have hcost₂' : c₂.bitOperations = c₁.bitOperations + carrySteps := by
    simpa [c₂, carrySteps, pass, adderCarrySteps] using hcost₂
  rcases hreturn with ⟨hrctl, hrregs, hrout, hrcalls, hrcost⟩
  have h6final : c₄.registers (adderReg 6) = addBitsAux false a b := by
    rw [hrregs]
    simpa [c₃, reverseSteps, hsum] using h6₃
  have h7final : c₄.registers (adderReg 7) = [true] := by
    rw [hrregs]
    simpa [c₃, reverseSteps] using h7₃
  have h8final : c₄.registers (adderReg 8) = [] := by
    rw [hrregs]
    simpa [c₃, reverseSteps] using h8₃
  have h9final : c₄.registers (adderReg 9) = c.registers (adderReg 9) := by
    rw [hrregs]
    calc
      c₃.registers (adderReg 9) = c₂.registers (adderReg 9) := h9₃
      _ = c₁.registers (adderReg 9) := by
        simpa [c₂, carrySteps, pass, adderCarrySteps] using h9₂
      _ = c.registers (adderReg 9) := by simpa [c₁] using h9₁
  have h3final : c₄.registers (adderReg 3) = c.registers (adderReg 3) := by
    rw [hrregs]
    calc
      c₃.registers (adderReg 3) = c₂.registers (adderReg 3) := hreg3₃
      _ = c₁.registers (adderReg 3) := by
        simpa [c₂, carrySteps, pass, adderCarrySteps] using hreg3₂
      _ = c.registers (adderReg 3) := by simpa [c₁] using hreg3₁
  have h4final : c₄.registers (adderReg 4) = c.registers (adderReg 4) := by
    rw [hrregs]
    calc
      c₃.registers (adderReg 4) = c₂.registers (adderReg 4) := hreg4₃
      _ = c₁.registers (adderReg 4) := by
        simpa [c₂, carrySteps, pass, adderCarrySteps] using hreg4₂
      _ = c.registers (adderReg 4) := by simpa [c₁] using hreg4₁
  have h5final : c₄.registers (adderReg 5) = c.registers (adderReg 5) := by
    rw [hrregs]
    calc
      c₃.registers (adderReg 5) = c₂.registers (adderReg 5) := hreg5₃
      _ = c₁.registers (adderReg 5) := by
        simpa [c₂, carrySteps, pass, adderCarrySteps] using hreg5₂
      _ = c.registers (adderReg 5) := by simpa [c₁] using hreg5₁
  have hcallsFinal : c₄.oracleCalls = c.oracleCalls := by
    calc
      c₄.oracleCalls = c₃.oracleCalls := hrcalls
      _ = c₂.oracleCalls := hcalls₃
      _ = c₁.oracleCalls := hcalls₂'
      _ = c.oracleCalls := hcalls₁'
  have hcostFinal : c₄.bitOperations = c.bitOperations + firstSteps + carrySteps + reverseSteps + 2 := by
    calc
      c₄.bitOperations = c₃.bitOperations + 2 := by simpa [c₄, c₃] using hrcost
      _ = c₂.bitOperations + reverseSteps + 2 := by
        have h : c₃.bitOperations = c₂.bitOperations + reverseSteps := by
          simpa [c₃, reverseSteps, Nat.add_assoc] using hcost₃
        rw [h]
      _ = c.bitOperations + firstSteps + carrySteps + reverseSteps + 2 := by
        rw [hcost₂', hcost₁']
  have hcompose := execution_append_three (binaryStackAdderWithCall P call) O c bits
    firstSteps carrySteps (reverseSteps + 2)
  have hsplit := execution_append (binaryStackAdderWithCall P call) O c₂
    (fun t => bits (firstSteps + carrySteps + t)) reverseSteps 2
  have htotal : adderTotalSteps a b + 1 = firstSteps + (carrySteps + (reverseSteps + 2)) := by
    dsimp [adderTotalSteps, adderCarrySteps, firstSteps, carrySteps,
      reverseSteps, scratch, adderFinalScratch]
    omega
  have htape :
      (fun t => bits (firstSteps + carrySteps + (reverseSteps + t))) =
        (fun t => bits (firstSteps + carrySteps + reverseSteps + t)) := by
    funext t
    congr 1
    omega
  have hrun : execution (binaryStackAdderWithCall P call) O c bits
        (adderTotalSteps a b + 1) = c₄ := by
    rw [htotal, hcompose, hsplit]
    simpa [c₂, c₃, c₄, firstSteps, carrySteps, reverseSteps, htape]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (execution (binaryStackAdderWithCall P call) O c bits
      (adderTotalSteps a b + 1)).control = _
    rw [hrun]
    exact hrctl
  · change (execution (binaryStackAdderWithCall P call) O c bits
      (adderTotalSteps a b + 1)).registers (adderReg 6) = _
    rw [hrun]
    exact h6final
  · change (execution (binaryStackAdderWithCall P call) O c bits
      (adderTotalSteps a b + 1)).registers (adderReg 7) = _
    rw [hrun]
    exact h7final
  · change (execution (binaryStackAdderWithCall P call) O c bits
      (adderTotalSteps a b + 1)).registers (adderReg 8) = _
    rw [hrun]
    exact h8final
  · change (execution (binaryStackAdderWithCall P call) O c bits
      (adderTotalSteps a b + 1)).registers (adderReg 9) = _
    rw [hrun]
    exact h9final
  · change (execution (binaryStackAdderWithCall P call) O c bits
      (adderTotalSteps a b + 1)).registers (adderReg 3) = _
    rw [hrun]
    exact h3final
  · change (execution (binaryStackAdderWithCall P call) O c bits
      (adderTotalSteps a b + 1)).registers (adderReg 4) = _
    rw [hrun]
    exact h4final
  · change (execution (binaryStackAdderWithCall P call) O c bits
      (adderTotalSteps a b + 1)).registers (adderReg 5) = _
    rw [hrun]
    exact h5final
  · change (execution (binaryStackAdderWithCall P call) O c bits
      (adderTotalSteps a b + 1)).output = none
    rw [hrun]
    exact hrout
  · change (execution (binaryStackAdderWithCall P call) O c bits
      (adderTotalSteps a b + 1)).oracleCalls = _
    rw [hrun]
    exact hcallsFinal
  · change (execution (binaryStackAdderWithCall P call) O c bits
      (adderTotalSteps a b + 1)).bitOperations = _
    rw [hrun]
    simpa [firstSteps, reverseSteps, Nat.add_assoc] using hcostFinal
/-- The call-enabled adder keeps the same linear input-width charge as the
standalone routine. -/
theorem binaryStackAdderWithCall_cost_le
    {s n : ℕ} (P : Program 2 s) (call : Fin (s + 1))
    (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 (s + 23)) (a b : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = adderWideState (adderState 0))
    (hleft : c.registers (adderReg 6) = a)
    (hright : c.registers (adderReg 7) = b)
    (hscratch : c.registers (adderReg 8) = []) :
    (execution (binaryStackAdderWithCall P call) O c bits
      (adderTotalSteps a b + 1)).bitOperations ≤
      c.bitOperations + 6 * max a.length b.length + 10 := by
  rcases binaryStackAdderWithCall_correct P call O bits c a b hout hcontrol
    hleft hright hscratch with ⟨_, _, _, _, _, _, _, _, _, _, hcost⟩
  have hcarry : adderCarrySteps a b ≤ 3 := by
    by_cases h : (addBitsPass false a b).2 <;> simp [adderCarrySteps, h]
  have hscratchLen := embedded_adderFinalScratch_length_le a b
  rw [hcost]
  omega

/-- A small continuation that consumes one unary loop-counter bit after each
addition, calls the adder again while bits remain, and halts when it is empty.
The call state's own instruction is unreachable: incoming targets are compiled
directly to adder entry state zero. -/
def unaryAdderLoopContinuation : Program 2 2 := fun q =>
  match q.val with
  | 0 => .pop (adderReg 9) ⟨2, by omega⟩ ⟨1, by omega⟩ ⟨1, by omega⟩
  | _ => .halt

def unaryAdderLoopProgram : Program 2 25 :=
  binaryStackAdderWithCall unaryAdderLoopContinuation ⟨1, by omega⟩

/-- The selected loop repeatedly adds one, so its exact result bits are a
binary encoding of the initial value plus the number of loop-counter bits and
the initial adder pass. -/
def unaryAdderLoopResultBits (a : List Bool) : List Bool → List Bool
  | [] => addBitsAux false a [true]
  | _ :: rest => unaryAdderLoopResultBits (addBitsAux false a [true]) rest

/-- Execution-step clock for the unary-counter repeated-adder program. -/
def unaryAdderLoopSteps (a : List Bool) : List Bool → ℕ
  | [] => adderTotalSteps a [true] + 3
  | _ :: rest => adderTotalSteps a [true] + 2 +
      unaryAdderLoopSteps (addBitsAux false a [true]) rest

/-- Exact bit-operation count. The empty-counter branch also charges for
writing the rational numerator and denominator. -/
def unaryAdderLoopBitOperations (a : List Bool) : List Bool → ℕ
  | [] => adderTotalSteps a [true] + (addBitsAux false a [true]).length + 4
  | _ :: rest => adderTotalSteps a [true] + 2 +
      unaryAdderLoopBitOperations (addBitsAux false a [true]) rest

/-- Arithmetic specification of the repeated increment loop. -/
theorem binaryValue_unaryAdderLoopResultBits (a counter : List Bool) :
    binaryValue (unaryAdderLoopResultBits a counter) =
      binaryValue a + counter.length + 1 := by
  induction counter generalizing a with
  | nil =>
      simp [unaryAdderLoopResultBits, binaryValue_addBitsAux, binaryValue]
  | cons bit rest ih =>
      rw [unaryAdderLoopResultBits, ih, binaryValue_addBitsAux]
      simp [List.length_cons, binaryValue]
      omega

private theorem addBitsAux_rhs_empty_length (carry : Bool) (a : List Bool) :
    (addBitsAux carry a []).length ≤ a.length + 1 := by
  induction a generalizing carry with
  | nil => cases carry <;> simp [addBitsAux]
  | cons bit rest ih =>
      simp only [addBitsAux, List.length_cons]
      exact Nat.succ_le_succ (ih (addColumn bit false carry).2)

private theorem increment_addBitsAux_length_le (a : List Bool) :
    (addBitsAux false a [true]).length ≤ a.length + 1 := by
  cases a with
  | nil => simp [addBitsAux, addColumn]
  | cons bit rest =>
      simp only [addBitsAux, List.length_cons]
      have h := addBitsAux_rhs_empty_length (addColumn bit true false).2 rest
      omega

theorem unaryAdderLoopResultBits_length_le (a counter : List Bool) :
    (unaryAdderLoopResultBits a counter).length ≤ a.length + counter.length + 1 := by
  induction counter generalizing a with
  | nil => simpa [unaryAdderLoopResultBits] using increment_addBitsAux_length_le a
  | cons bit rest ih =>
      rw [unaryAdderLoopResultBits]
      have hinc := increment_addBitsAux_length_le a
      have htail := ih (addBitsAux false a [true])
      simp only [List.length_cons]
      omega

theorem unaryAdderLoopBitOperations_le_quadratic
    (a counter : List Bool) :
    unaryAdderLoopBitOperations a counter ≤
      100 * (counter.length + 1) * (a.length + counter.length + 5) := by
  induction counter generalizing a with
  | nil =>
      have hcarry : adderCarrySteps a [true] ≤ 3 := by
        by_cases h : (addBitsPass false a [true]).2 <;>
          simp [adderCarrySteps, h]
      have hmax : max a.length 1 ≤ a.length + 1 := by omega
      have hscratch := embedded_adderFinalScratch_length_le a [true]
      have hinc := increment_addBitsAux_length_le a
      have hscratch' : (adderFinalScratch a [true]).length ≤ a.length + 2 := by
        have h := hscratch
        simp only [List.length_singleton] at h
        omega
      dsimp [unaryAdderLoopBitOperations, adderTotalSteps]
      omega
  | cons bit rest ih =>
      have hsteps : adderTotalSteps a [true] ≤ 5 * a.length + 13 := by
        have hcarry : adderCarrySteps a [true] ≤ 3 := by
          by_cases h : (addBitsPass false a [true]).2 <;>
            simp [adderCarrySteps, h]
        have hmax : max a.length 1 ≤ a.length + 1 := by omega
        have hscratch := embedded_adderFinalScratch_length_le a [true]
        dsimp [adderTotalSteps]
        simp only [List.length_singleton] at hcarry hscratch ⊢
        omega
      have hinc := increment_addBitsAux_length_le a
      have htail := ih (addBitsAux false a [true])
      have htail' : unaryAdderLoopBitOperations (addBitsAux false a [true]) rest ≤
          100 * (rest.length + 1) * (a.length + rest.length + 6) := by
        have hwidth : (addBitsAux false a [true]).length + rest.length + 5 ≤
            a.length + rest.length + 6 := by omega
        calc
          unaryAdderLoopBitOperations (addBitsAux false a [true]) rest ≤
              100 * (rest.length + 1) *
                ((addBitsAux false a [true]).length + rest.length + 5) := htail
          _ ≤ 100 * (rest.length + 1) * (a.length + rest.length + 6) :=
            Nat.mul_le_mul_left _ hwidth
      simp only [unaryAdderLoopBitOperations, List.length_cons]
      nlinarith

/-- The loop's counter check either exits to the halt after its last adder
call, or consumes one bit and returns to adder entry. -/
theorem unaryAdderLoopProgram_counter_step
    {n : ℕ} (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 25) (bit : Bool) (rest : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = ⟨23, by omega⟩)
    (hcounter : c.registers (adderReg 9) = bit :: rest) :
    let out := execution unaryAdderLoopProgram O c bits 1
    out.control = ⟨0, by omega⟩ ∧
    out.registers = Function.update c.registers (adderReg 9) rest ∧
    out.registers (adderReg 9) = rest ∧ out.output = none ∧
    out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 1 := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  simp only at hout hcontrol hcounter
  subst control
  subst output
  simp [adderReg] at hcounter
  simp [execution, machineStep, unaryAdderLoopProgram,
    binaryStackAdderWithCall, unaryAdderLoopContinuation,
    adderCallInstruction, adderCallTarget, adderReg, hcounter,
    Function.update]

theorem unaryAdderLoopProgram_empty_exit
    {n : ℕ} (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 25) (hout : c.output = none)
    (hcontrol : c.control = ⟨23, by omega⟩)
    (hcounter : c.registers (adderReg 9) = []) :
    let out := execution unaryAdderLoopProgram O c bits 2
    out.control = ⟨25, by omega⟩ ∧
    out.output = some ((binaryValue (c.registers (adderReg 6)) : ℚ) /
      (binaryValue (c.registers (adderReg 7)) : ℚ)) ∧
    out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations +
      (c.registers (adderReg 6)).length + (c.registers (adderReg 7)).length + 2 := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  simp only at hout hcontrol hcounter
  subst control
  subst output
  simp [adderReg] at hcounter
  simp [execution, machineStep, unaryAdderLoopProgram,
    binaryStackAdderWithCall, unaryAdderLoopContinuation,
    adderCallInstruction, adderCallTarget, adderReg, hcounter,
    Function.update, Nat.add_assoc] <;> omega

/-- The repeated-increment example really runs as one fixed machine program:
it adds one initially and once for each counter bit, then writes the exact
result as a rational with denominator one. -/
theorem unaryAdderLoopProgram_correct
    {n : ℕ} (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 25) (a counter : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = ⟨0, by omega⟩)
    (hleft : c.registers (adderReg 6) = a)
    (hright : c.registers (adderReg 7) = [true])
    (hscratch : c.registers (adderReg 8) = [])
    (hcounter : c.registers (adderReg 9) = counter) :
    let out := execution unaryAdderLoopProgram O c bits (unaryAdderLoopSteps a counter)
    out.control = ⟨25, by omega⟩ ∧
    out.output = some ((binaryValue (unaryAdderLoopResultBits a counter) : ℚ) / 1) ∧
    out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + unaryAdderLoopBitOperations a counter := by
  induction counter generalizing a c bits with
  | nil =>
      have hadd := binaryStackAdderWithCall_correct unaryAdderLoopContinuation
        ⟨1, by omega⟩ O bits c a [true] hout hcontrol hleft hright hscratch
      rcases hadd with ⟨hctl₁, h6₁, h7₁, h8₁, h9₁, hreg3₁, hreg4₁, hreg5₁, hout₁, hcalls₁, hcost₁⟩
      let c₁ := execution unaryAdderLoopProgram O c bits (adderTotalSteps a [true] + 1)
      have hcounter₁ : c₁.registers (adderReg 9) = [] := by
        simpa [c₁, unaryAdderLoopProgram] using h9₁.trans hcounter
      have hexit := unaryAdderLoopProgram_empty_exit O
        (fun t => bits (adderTotalSteps a [true] + 1 + t)) c₁
        hout₁ hctl₁ hcounter₁
      rcases hexit with ⟨hctl₂, hout₂, hcalls₂, hcost₂⟩
      have htotal : unaryAdderLoopSteps a [] =
          (adderTotalSteps a [true] + 1) + 2 := by
        simp [unaryAdderLoopSteps, Nat.add_assoc]
      have hrun₀ := execution_append unaryAdderLoopProgram O c bits
        (adderTotalSteps a [true] + 1) 2
      have hrun : execution unaryAdderLoopProgram O c bits (unaryAdderLoopSteps a []) =
          execution unaryAdderLoopProgram O c₁
            (fun t => bits (adderTotalSteps a [true] + 1 + t)) 2 := by
        simpa [unaryAdderLoopSteps, c₁, Nat.add_assoc] using hrun₀
      have hcost₁' : c₁.bitOperations =
          c.bitOperations + (adderTotalSteps a [true] + 1) := by
        simpa [c₁, unaryAdderLoopProgram, adderTotalSteps, adderCarrySteps,
          Nat.add_assoc] using hcost₁
      have hresult : c₁.registers (adderReg 6) = addBitsAux false a [true] := by
        simpa [c₁, unaryAdderLoopProgram] using h6₁
      have hden : c₁.registers (adderReg 7) = [true] := by
        simpa [c₁, unaryAdderLoopProgram] using h7₁
      refine ⟨?_, ?_, ?_, ?_⟩
      · change (execution unaryAdderLoopProgram O c bits
          (unaryAdderLoopSteps a [])).control = _
        rw [hrun]
        exact hctl₂
      · change (execution unaryAdderLoopProgram O c bits
          (unaryAdderLoopSteps a [])).output = _
        rw [hrun]
        rw [hout₂, hresult, hden]
        norm_num [unaryAdderLoopResultBits, binaryValue]
      · change (execution unaryAdderLoopProgram O c bits
          (unaryAdderLoopSteps a [])).oracleCalls = _
        rw [hrun]
        calc
          (execution unaryAdderLoopProgram O c₁
              (fun t => bits (adderTotalSteps a [true] + 1 + t)) 2).oracleCalls =
              c₁.oracleCalls := hcalls₂
          _ = c.oracleCalls := by
            simpa [c₁, unaryAdderLoopProgram] using hcalls₁
      · change (execution unaryAdderLoopProgram O c bits
          (unaryAdderLoopSteps a [])).bitOperations = _
        rw [hrun]
        have hlen : (c₁.registers (adderReg 6)).length =
            (addBitsAux false a [true]).length := by rw [hresult]
        have hcost₂' := hcost₂
        rw [hresult, hden] at hcost₂'
        rw [hcost₂', hcost₁']
        simp [unaryAdderLoopBitOperations, Nat.add_assoc]
        omega
  | cons bit rest ih =>
      let adderSteps := adderTotalSteps a [true] + 1
      let a' := addBitsAux false a [true]
      have hadd := binaryStackAdderWithCall_correct unaryAdderLoopContinuation
        ⟨1, by omega⟩ O bits c a [true] hout hcontrol hleft hright hscratch
      rcases hadd with ⟨hctl₁, h6₁, h7₁, h8₁, h9₁, hreg3₁, hreg4₁, hreg5₁, hout₁, hcalls₁, hcost₁⟩
      let c₁ := execution unaryAdderLoopProgram O c bits adderSteps
      have hcounter₁ : c₁.registers (adderReg 9) = bit :: rest := by
        simpa [c₁, unaryAdderLoopProgram, adderSteps] using h9₁.trans hcounter
      have h6₁' : c₁.registers (adderReg 6) = a' := by
        simpa [c₁, unaryAdderLoopProgram, a', adderSteps] using h6₁
      have h7₁' : c₁.registers (adderReg 7) = [true] := by
        simpa [c₁, unaryAdderLoopProgram, adderSteps] using h7₁
      have h8₁' : c₁.registers (adderReg 8) = [] := by
        simpa [c₁, unaryAdderLoopProgram, adderSteps] using h8₁
      have hstep := unaryAdderLoopProgram_counter_step O
        (fun t => bits (adderSteps + t)) c₁ bit rest hout₁ hctl₁ hcounter₁
      rcases hstep with ⟨hctl₂, hregs₂, hcounter₂, hout₂, hcalls₂, hcost₂⟩
      let c₂ := execution unaryAdderLoopProgram O c₁
        (fun t => bits (adderSteps + t)) 1
      have hleft₂ : c₂.registers (adderReg 6) = a' := by
        calc
          c₂.registers (adderReg 6) = (Function.update c₁.registers
              (adderReg 9) rest) (adderReg 6) := by rw [hregs₂]
          _ = c₁.registers (adderReg 6) := by simp [adderReg]
          _ = a' := h6₁'
      have hright₂ : c₂.registers (adderReg 7) = [true] := by
        calc
          c₂.registers (adderReg 7) = (Function.update c₁.registers
              (adderReg 9) rest) (adderReg 7) := by rw [hregs₂]
          _ = c₁.registers (adderReg 7) := by simp [adderReg]
          _ = [true] := h7₁'
      have hcounter₂' : c₂.registers (adderReg 9) = rest := by
        simpa [c₂] using hcounter₂
      have hscratch₂ : c₂.registers (adderReg 8) = [] := by
        calc
          c₂.registers (adderReg 8) = (Function.update c₁.registers
              (adderReg 9) rest) (adderReg 8) := by rw [hregs₂]
          _ = c₁.registers (adderReg 8) := by simp [adderReg]
          _ = [] := h8₁'
      have htail := ih (a := a') (c := c₂)
        (bits := fun t => bits (adderSteps + 1 + t)) hout₂ hctl₂
        hleft₂ hright₂ hscratch₂ hcounter₂'
      rcases htail with ⟨hctl₃, hout₃, hcalls₃, hcost₃⟩
      have htotal : unaryAdderLoopSteps a (bit :: rest) =
          adderSteps + (1 + unaryAdderLoopSteps a' rest) := by
        simp [unaryAdderLoopSteps, adderSteps, a', Nat.add_assoc]
        omega
      have hcompose := execution_append_three unaryAdderLoopProgram O c bits
        adderSteps 1 (unaryAdderLoopSteps a' rest)
      have hrun : execution unaryAdderLoopProgram O c bits
          (unaryAdderLoopSteps a (bit :: rest)) =
          execution unaryAdderLoopProgram O c₂
            (fun t => bits (adderSteps + 1 + t)) (unaryAdderLoopSteps a' rest) := by
        rw [htotal, hcompose]
      have hcost₁' : c₁.bitOperations = c.bitOperations + adderSteps := by
        simpa [c₁, unaryAdderLoopProgram, adderSteps, adderTotalSteps,
          adderCarrySteps, Nat.add_assoc] using hcost₁
      refine ⟨?_, ?_, ?_, ?_⟩
      · change (execution unaryAdderLoopProgram O c bits
          (unaryAdderLoopSteps a (bit :: rest))).control = _
        rw [hrun]
        exact hctl₃
      · change (execution unaryAdderLoopProgram O c bits
          (unaryAdderLoopSteps a (bit :: rest))).output = _
        rw [hrun]
        simpa [unaryAdderLoopResultBits, a'] using hout₃
      · change (execution unaryAdderLoopProgram O c bits
          (unaryAdderLoopSteps a (bit :: rest))).oracleCalls = _
        rw [hrun]
        calc
          (execution unaryAdderLoopProgram O c₂
              (fun t => bits (adderSteps + 1 + t)) (unaryAdderLoopSteps a' rest)).oracleCalls =
              c₂.oracleCalls := hcalls₃
          _ = c₁.oracleCalls := by simpa [c₂] using hcalls₂
          _ = c.oracleCalls := by simpa [c₁, unaryAdderLoopProgram, adderSteps] using hcalls₁
      · change (execution unaryAdderLoopProgram O c bits
          (unaryAdderLoopSteps a (bit :: rest))).bitOperations = _
        rw [hrun]
        rw [hcost₃]
        rw [show c₂.bitOperations = c₁.bitOperations + 1 by simpa [c₂] using hcost₂]
        rw [hcost₁']
        simp [unaryAdderLoopBitOperations, a', adderSteps, Nat.add_assoc]

/-- The call target itself returns to the embedded adder's entry state. -/
theorem adderCallTarget_call {s : ℕ} (call : Fin (s + 1)) :
    adderCallTarget call call = (⟨0, by omega⟩ : Fin (s + 24)) := by
  simp [adderCallTarget]

/-- After each addition, the example continuation consumes the unary counter;
an empty counter exits to the halt, while either bit loops to adder entry. -/
theorem unaryAdderLoopProgram_return_instruction :
    unaryAdderLoopProgram ⟨23, by omega⟩ =
      .pop (adderReg 9) ⟨25, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩ := by
  simp [unaryAdderLoopProgram, binaryStackAdderWithCall,
    unaryAdderLoopContinuation, adderCallInstruction, adderCallTarget,
    adderReg]

/-- Continuation for binary shift-and-add multiplication. Register 5 retains
the multiplicand, register 9 is the little-endian multiplier, register 6 is
the accumulator, register 4 is a temporary copy stack, and register 3 marks a
return from an adder call. The designated continuation state 1 is compiled as
a call to the fixed adder entry. -/
def binaryMultiplierContinuation : Program 2 14 := fun q =>
  match q.val with
  | 0 => .pop (adderReg 3) ⟨2, by omega⟩ ⟨2, by omega⟩ ⟨14, by omega⟩
  | 1 => .halt
  | 2 => .pop (adderReg 9) ⟨13, by omega⟩ ⟨14, by omega⟩ ⟨3, by omega⟩
  | 3 => .pop (adderReg 7) ⟨4, by omega⟩ ⟨4, by omega⟩ ⟨4, by omega⟩
  | 4 => .pop (adderReg 5) ⟨7, by omega⟩ ⟨5, by omega⟩ ⟨6, by omega⟩
  | 5 => .push (adderReg 4) false ⟨4, by omega⟩
  | 6 => .push (adderReg 4) true ⟨4, by omega⟩
  | 7 => .pop (adderReg 4) ⟨8, by omega⟩ ⟨9, by omega⟩ ⟨10, by omega⟩
  | 8 => .push (adderReg 3) true ⟨1, by omega⟩
  | 9 => .push (adderReg 5) false ⟨11, by omega⟩
  | 10 => .push (adderReg 5) true ⟨12, by omega⟩
  | 11 => .push (adderReg 7) false ⟨7, by omega⟩
  | 12 => .push (adderReg 7) true ⟨7, by omega⟩
  | 13 => .halt
  | 14 => .push (adderReg 5) false ⟨2, by omega⟩
  | _ => .halt

/-- One fixed binary multiplication program assembled from the verified
call-enabled binary adder. -/
def binaryStackMultiplierProgram : Program 2 37 :=
  binaryStackAdderWithCall binaryMultiplierContinuation ⟨1, by omega⟩

theorem binaryStackMultiplierProgram_entry_instruction :
    binaryStackMultiplierProgram ⟨23, by omega⟩ =
      .pop (adderReg 3) ⟨25, by omega⟩ ⟨25, by omega⟩ ⟨37, by omega⟩ := by
  norm_num [binaryStackMultiplierProgram, binaryStackAdderWithCall,
    binaryMultiplierContinuation, adderCallInstruction, adderCallTarget, adderReg]

theorem binaryStackMultiplierProgram_unreachable_call_state :
    binaryStackMultiplierProgram ⟨24, by omega⟩ =
      .halt := by
  norm_num [binaryStackMultiplierProgram, binaryStackAdderWithCall,
    binaryMultiplierContinuation, adderCallInstruction, adderCallTarget]

theorem binaryStackMultiplierProgram_final_halt :
    binaryStackMultiplierProgram ⟨36, by omega⟩ = .halt := by
  norm_num [binaryStackMultiplierProgram, binaryStackAdderWithCall,
    binaryMultiplierContinuation, adderCallInstruction, adderCallTarget, adderReg]

/-- Arithmetic specification of the binary shift-and-add loop. -/
def binaryStackMultiplierResultBits (acc multiplicand : List Bool) :
    List Bool → List Bool
  | [] => acc
  | bit :: rest =>
      binaryStackMultiplierResultBits
        (if bit then addBitsAux false acc multiplicand else acc)
        (false :: multiplicand) rest

/-- Exact instruction count of the fixed multiplier loop from control state
25, including the final halt. -/
def binaryStackMultiplierLoopSteps (acc multiplicand : List Bool) :
    List Bool → ℕ
  | [] => 2
  | bit :: rest =>
      (if bit then 5 * multiplicand.length + adderTotalSteps acc multiplicand + 8
       else 2) +
        binaryStackMultiplierLoopSteps
          (if bit then addBitsAux false acc multiplicand else acc)
          (false :: multiplicand) rest

/-- Exact accumulated bit-operation charge of the same loop. -/
def binaryStackMultiplierLoopBitOperations (acc multiplicand : List Bool) :
    List Bool → ℕ
  | [] => acc.length + 3
  | bit :: rest =>
      (if bit then 5 * multiplicand.length +
          3 * max acc.length multiplicand.length + adderCarrySteps acc multiplicand +
          2 * (adderFinalScratch acc multiplicand).length + 11
       else 2) +
        binaryStackMultiplierLoopBitOperations
          (if bit then addBitsAux false acc multiplicand else acc)
          (false :: multiplicand) rest

theorem binaryValue_binaryStackMultiplierResultBits
    (acc multiplicand multiplier : List Bool) :
    binaryValue (binaryStackMultiplierResultBits acc multiplicand multiplier) =
      binaryValue acc + binaryValue multiplicand * binaryValue multiplier := by
  induction multiplier generalizing acc multiplicand with
  | nil => simp [binaryStackMultiplierResultBits, binaryValue]
  | cons bit rest ih =>
      cases bit
      · simp only [binaryStackMultiplierResultBits, if_false]
        rw [ih]
        simp [binaryValue]
        ring
      · simp only [binaryStackMultiplierResultBits, if_true]
        rw [ih, binaryValue_addBitsAux]
        simp [binaryValue]
        ring

/-- A multiplier copy-loop column transfers one source bit to the temporary
stack and returns to the same loop state. -/
theorem binaryStackMultiplierProgram_copyToTemp_column
    {n : ℕ} (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 37) (bit : Bool) (rest temp : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = ⟨27, by omega⟩)
    (hsource : c.registers (adderReg 5) = bit :: rest)
    (htemp : c.registers (adderReg 4) = temp) :
    let out := execution binaryStackMultiplierProgram O c bits 2
    out.control = ⟨27, by omega⟩ ∧
    out.registers (adderReg 5) = rest ∧
    out.registers (adderReg 4) = bit :: temp ∧
    out.registers (adderReg 7) = c.registers (adderReg 7) ∧
    out.registers (adderReg 3) = c.registers (adderReg 3) ∧
    out.registers (adderReg 6) = c.registers (adderReg 6) ∧
    out.registers (adderReg 8) = c.registers (adderReg 8) ∧
    out.registers (adderReg 9) = c.registers (adderReg 9) ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 2 := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  simp only at hout hcontrol hsource htemp
  subst control
  subst output
  simp [adderReg] at hsource htemp
  cases bit <;>
    simp [execution, machineStep, binaryStackMultiplierProgram,
      binaryStackAdderWithCall, binaryMultiplierContinuation,
      adderCallInstruction, adderCallTarget, adderReg,
      hsource, htemp, Function.update]

/-- The first half of copying a multiplicand reverses it onto the temporary
stack while consuming the source stack. -/
theorem binaryStackMultiplierProgram_copyToTemp
    {n : ℕ} (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 37) (source temp : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = ⟨27, by omega⟩)
    (hsource : c.registers (adderReg 5) = source)
    (htemp : c.registers (adderReg 4) = temp) :
    let out := execution binaryStackMultiplierProgram O c bits (2 * source.length + 1)
    out.control = ⟨30, by omega⟩ ∧
    out.registers (adderReg 5) = [] ∧
    out.registers (adderReg 4) = source.reverse ++ temp ∧
    out.registers (adderReg 7) = c.registers (adderReg 7) ∧
    out.registers (adderReg 3) = c.registers (adderReg 3) ∧
    out.registers (adderReg 6) = c.registers (adderReg 6) ∧
    out.registers (adderReg 8) = c.registers (adderReg 8) ∧
    out.registers (adderReg 9) = c.registers (adderReg 9) ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 2 * source.length + 1 := by
  induction source generalizing c bits temp with
  | nil =>
      rcases c with ⟨regs, control, output, calls, ops⟩
      simp only at hout hcontrol hsource htemp
      subst control
      subst output
      simp [adderReg] at hsource htemp
      simp [execution, machineStep, binaryStackMultiplierProgram,
        binaryStackAdderWithCall, binaryMultiplierContinuation,
        adderCallInstruction, adderCallTarget, adderReg,
        hsource, htemp, Function.update]
  | cons bit rest ih =>
      simp only [List.length_cons]
      have hstep := binaryStackMultiplierProgram_copyToTemp_column O bits c bit rest temp
        hout hcontrol hsource htemp
      rcases hstep with ⟨hctl, hsource', htemp', hdest', hreg3', hreg6', hreg8', hreg9', hout', hcalls', hcost'⟩
      let c' := execution binaryStackMultiplierProgram O c bits 2
      have htail := ih (c := c') (bits := fun t => bits (2 + t))
        (temp := bit :: temp) hout' hctl hsource' htemp'
      rw [show 2 * (rest.length + 1) + 1 = 2 + (2 * rest.length + 1) by omega,
        execution_append]
      simp_all [c', List.reverse_cons, List.append_assoc, Nat.add_assoc] <;> omega

/-- One return-copy column restores a source bit and pushes the same bit onto
the adder's second input stack. -/
theorem binaryStackMultiplierProgram_copyBack_column
    {n : ℕ} (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 37) (bit : Bool) (rest source dest : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = ⟨30, by omega⟩)
    (htemp : c.registers (adderReg 4) = bit :: rest)
    (hsource : c.registers (adderReg 5) = source)
    (hdest : c.registers (adderReg 7) = dest) :
    let out := execution binaryStackMultiplierProgram O c bits 3
    out.control = ⟨30, by omega⟩ ∧
    out.registers (adderReg 4) = rest ∧
    out.registers (adderReg 5) = bit :: source ∧
    out.registers (adderReg 7) = bit :: dest ∧
    out.registers (adderReg 3) = c.registers (adderReg 3) ∧
    out.registers (adderReg 6) = c.registers (adderReg 6) ∧
    out.registers (adderReg 8) = c.registers (adderReg 8) ∧
    out.registers (adderReg 9) = c.registers (adderReg 9) ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 3 := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  simp only at hout hcontrol htemp hsource hdest
  subst control
  subst output
  simp [adderReg] at htemp hsource hdest
  cases bit <;>
    simp [execution, machineStep, binaryStackMultiplierProgram,
      binaryStackAdderWithCall, binaryMultiplierContinuation,
      adderCallInstruction, adderCallTarget, adderReg,
      htemp, hsource, hdest, Function.update]

/-- The second copy pass reconstructs the multiplicand in register 5 and
forms an identical little-endian stack in the adder's register 7. -/
theorem binaryStackMultiplierProgram_copyBack
    {n : ℕ} (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 37) (temp source dest : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = ⟨30, by omega⟩)
    (htemp : c.registers (adderReg 4) = temp)
    (hsource : c.registers (adderReg 5) = source)
    (hdest : c.registers (adderReg 7) = dest) :
    let out := execution binaryStackMultiplierProgram O c bits (3 * temp.length + 1)
    out.control = ⟨31, by omega⟩ ∧
    out.registers (adderReg 4) = [] ∧
    out.registers (adderReg 5) = temp.reverse ++ source ∧
    out.registers (adderReg 7) = temp.reverse ++ dest ∧
    out.registers (adderReg 3) = c.registers (adderReg 3) ∧
    out.registers (adderReg 6) = c.registers (adderReg 6) ∧
    out.registers (adderReg 8) = c.registers (adderReg 8) ∧
    out.registers (adderReg 9) = c.registers (adderReg 9) ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 3 * temp.length + 1 := by
  induction temp generalizing c bits source dest with
  | nil =>
      rcases c with ⟨regs, control, output, calls, ops⟩
      simp only at hout hcontrol htemp hsource hdest
      subst control
      subst output
      simp [adderReg] at htemp hsource hdest
      simp [execution, machineStep, binaryStackMultiplierProgram,
        binaryStackAdderWithCall, binaryMultiplierContinuation,
        adderCallInstruction, adderCallTarget, adderReg,
        htemp, hsource, hdest, Function.update]
  | cons bit rest ih =>
      simp only [List.length_cons]
      have hstep := binaryStackMultiplierProgram_copyBack_column O bits c bit rest source dest
        hout hcontrol htemp hsource hdest
      rcases hstep with ⟨hctl, htemp', hsource', hdest', hreg3', hreg6', hreg8', hreg9', hout', hcalls', hcost'⟩
      let c' := execution binaryStackMultiplierProgram O c bits 3
      have htail := ih (c := c') (bits := fun t => bits (3 + t))
        (source := bit :: source) (dest := bit :: dest)
        hout' hctl htemp' hsource' hdest'
      rw [show 3 * (rest.length + 1) + 1 = 3 + (3 * rest.length + 1) by omega,
        execution_append]
      simp_all [c', List.reverse_cons, List.append_assoc, Nat.add_assoc] <;> omega

/-- The complete copy routine preserves register 5 and leaves an exact copy
of its original stack in register 7, ready for the adder call. -/
theorem binaryStackMultiplierProgram_copy
    {n : ℕ} (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 37) (source dest : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = ⟨27, by omega⟩)
    (hsource : c.registers (adderReg 5) = source)
    (htemp : c.registers (adderReg 4) = [])
    (hdest : c.registers (adderReg 7) = dest) :
    let out := execution binaryStackMultiplierProgram O c bits
      (5 * source.length + 2)
    out.control = ⟨31, by omega⟩ ∧
    out.registers (adderReg 4) = [] ∧
    out.registers (adderReg 5) = source ∧
    out.registers (adderReg 7) = source ++ dest ∧
    out.registers (adderReg 3) = c.registers (adderReg 3) ∧
    out.registers (adderReg 6) = c.registers (adderReg 6) ∧
    out.registers (adderReg 8) = c.registers (adderReg 8) ∧
    out.registers (adderReg 9) = c.registers (adderReg 9) ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 5 * source.length + 2 := by
  have hfirst := binaryStackMultiplierProgram_copyToTemp O bits c source []
    hout hcontrol hsource htemp
  rcases hfirst with ⟨hctl₁, hsource₁, htemp₁, hdestFirst, hreg3₁, hreg6₁, hreg8₁, hreg9₁, hout₁, hcalls₁, hcost₁⟩
  let c₁ := execution binaryStackMultiplierProgram O c bits (2 * source.length + 1)
  have hdest₁ : c₁.registers (adderReg 7) = dest := by
    simpa [c₁] using hdestFirst.trans hdest
  have hsecond := binaryStackMultiplierProgram_copyBack O
    (fun t => bits (2 * source.length + 1 + t)) c₁ source.reverse [] dest
    hout₁ hctl₁ (by simpa using htemp₁) hsource₁ hdest₁
  rcases hsecond with ⟨hctl₂, htemp₂, hsource₂, hdest₂, hreg3₂, hreg6₂, hreg8₂, hreg9₂, hout₂, hcalls₂, hcost₂⟩
  simp only [List.length_reverse] at hctl₂ htemp₂ hsource₂ hdest₂ hout₂ hcalls₂ hcost₂
  have htotal : 5 * source.length + 2 =
      (2 * source.length + 1) + (3 * source.length + 1) := by omega
  have hrun := execution_append binaryStackMultiplierProgram O c bits
    (2 * source.length + 1) (3 * source.length + 1)
  rw [← htotal] at hrun
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * source.length + 2)).control = _
    rw [hrun]
    simpa [c₁] using hctl₂
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * source.length + 2)).registers (adderReg 4) = _
    rw [hrun]
    simpa [c₁] using htemp₂
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * source.length + 2)).registers (adderReg 5) = _
    rw [hrun]
    simpa [c₁, List.reverse_reverse] using hsource₂
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * source.length + 2)).registers (adderReg 7) = _
    rw [hrun]
    simpa [c₁, List.reverse_reverse] using hdest₂
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * source.length + 2)).registers (adderReg 3) = _
    rw [hrun]
    calc
      (execution binaryStackMultiplierProgram O c₁
        (fun t => bits (2 * source.length + 1 + t)) (3 * source.length + 1)).registers
          (adderReg 3) = c₁.registers (adderReg 3) := by
        simpa [List.length_reverse] using hreg3₂
      _ = c.registers (adderReg 3) := by simpa [c₁] using hreg3₁
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * source.length + 2)).registers (adderReg 6) = _
    rw [hrun]
    calc
      (execution binaryStackMultiplierProgram O c₁
        (fun t => bits (2 * source.length + 1 + t)) (3 * source.length + 1)).registers
          (adderReg 6) = c₁.registers (adderReg 6) := by
        simpa [List.length_reverse] using hreg6₂
      _ = c.registers (adderReg 6) := by simpa [c₁] using hreg6₁
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * source.length + 2)).registers (adderReg 8) = _
    rw [hrun]
    calc
      (execution binaryStackMultiplierProgram O c₁
        (fun t => bits (2 * source.length + 1 + t)) (3 * source.length + 1)).registers
          (adderReg 8) = c₁.registers (adderReg 8) := by
        simpa [List.length_reverse] using hreg8₂
      _ = c.registers (adderReg 8) := by simpa [c₁] using hreg8₁
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * source.length + 2)).registers (adderReg 9) = _
    rw [hrun]
    calc
      (execution binaryStackMultiplierProgram O c₁
        (fun t => bits (2 * source.length + 1 + t)) (3 * source.length + 1)).registers
          (adderReg 9) = c₁.registers (adderReg 9) := by
        simpa [List.length_reverse] using hreg9₂
      _ = c.registers (adderReg 9) := by simpa [c₁] using hreg9₁
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * source.length + 2)).output = none
    rw [hrun]
    simpa [c₁] using hout₂
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * source.length + 2)).oracleCalls = c.oracleCalls
    rw [hrun]
    simpa [c₁] using hcalls₂.trans hcalls₁
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * source.length + 2)).bitOperations = _
    rw [hrun]
    calc
      (execution binaryStackMultiplierProgram O c₁
          (fun t => bits (2 * source.length + 1 + t)) (3 * source.length + 1)).bitOperations =
          c₁.bitOperations + (3 * source.length + 1) := by
            simpa [Nat.add_assoc] using hcost₂
      _ = c.bitOperations + (2 * source.length + 1) + (3 * source.length + 1) := by
          rw [show c₁.bitOperations = c.bitOperations + (2 * source.length + 1) by
            simpa [c₁, Nat.add_assoc] using hcost₁]
      _ = c.bitOperations + 5 * source.length + 2 := by omega

/-- A zero multiplier bit performs no addition: it consumes the bit, shifts
the multiplicand left, and returns to the multiplier loop. -/
theorem binaryStackMultiplierProgram_zero_bit
    {n : ℕ} (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 37) (acc multiplicand rest : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = ⟨25, by omega⟩)
    (hacc : c.registers (adderReg 6) = acc)
    (hmult : c.registers (adderReg 5) = multiplicand)
    (hcounter : c.registers (adderReg 9) = false :: rest) :
    let out := execution binaryStackMultiplierProgram O c bits 2
    out.control = ⟨25, by omega⟩ ∧
    out.registers (adderReg 6) = acc ∧
    out.registers (adderReg 5) = false :: multiplicand ∧
    out.registers (adderReg 9) = rest ∧
    out.registers (adderReg 3) = c.registers (adderReg 3) ∧
    out.registers (adderReg 4) = c.registers (adderReg 4) ∧
    out.registers (adderReg 7) = c.registers (adderReg 7) ∧
    out.registers (adderReg 8) = c.registers (adderReg 8) ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 2 := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  simp only at hout hcontrol hacc hmult hcounter
  subst control
  subst output
  simp [adderReg] at hacc hmult hcounter
  simp [execution, machineStep, binaryStackMultiplierProgram,
    binaryStackAdderWithCall, binaryMultiplierContinuation,
    adderCallInstruction, adderCallTarget, adderReg,
    hacc, hmult, hcounter, Function.update]

/-- Entering the true-bit path consumes its multiplier bit and the adder's
denominator marker before copying the multiplicand. -/
theorem binaryStackMultiplierProgram_true_setup
    {n : ℕ} (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 37) (acc multiplicand rest : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = ⟨25, by omega⟩)
    (hacc : c.registers (adderReg 6) = acc)
    (hmult : c.registers (adderReg 5) = multiplicand)
    (htemp : c.registers (adderReg 4) = [])
    (hmarker : c.registers (adderReg 3) = [])
    (hden : c.registers (adderReg 7) = [true])
    (hcounter : c.registers (adderReg 9) = true :: rest) :
    let out := execution binaryStackMultiplierProgram O c bits 2
    out.control = ⟨27, by omega⟩ ∧
    out.registers (adderReg 6) = acc ∧
    out.registers (adderReg 5) = multiplicand ∧
    out.registers (adderReg 4) = [] ∧
    out.registers (adderReg 3) = [] ∧
    out.registers (adderReg 7) = [] ∧
    out.registers (adderReg 9) = rest ∧
    out.registers (adderReg 8) = c.registers (adderReg 8) ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 2 := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  simp only at hout hcontrol hacc hmult htemp hmarker hden hcounter
  subst control
  subst output
  simp [adderReg] at hacc hmult htemp hmarker hden hcounter
  simp [execution, machineStep, binaryStackMultiplierProgram,
    binaryStackAdderWithCall, binaryMultiplierContinuation,
    adderCallInstruction, adderCallTarget, adderReg,
    hacc, hmult, htemp, hmarker, hden, hcounter, Function.update]

/-- Consume a true multiplier bit and duplicate the multiplicand while
retaining the accumulator and the remaining multiplier. The resulting state
is the exact input expected by the adder call. -/
theorem binaryStackMultiplierProgram_true_ready
    {n : ℕ} (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 37) (acc multiplicand rest : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = ⟨25, by omega⟩)
    (hacc : c.registers (adderReg 6) = acc)
    (hmult : c.registers (adderReg 5) = multiplicand)
    (htemp : c.registers (adderReg 4) = [])
    (hmarker : c.registers (adderReg 3) = [])
    (hden : c.registers (adderReg 7) = [true])
    (hscratch : c.registers (adderReg 8) = [])
    (hcounter : c.registers (adderReg 9) = true :: rest) :
    let out := execution binaryStackMultiplierProgram O c bits
      (5 * multiplicand.length + 4)
    out.control = ⟨31, by omega⟩ ∧
    out.registers (adderReg 3) = [] ∧
    out.registers (adderReg 4) = [] ∧
    out.registers (adderReg 5) = multiplicand ∧
    out.registers (adderReg 6) = acc ∧
    out.registers (adderReg 7) = multiplicand ∧
    out.registers (adderReg 8) = [] ∧
    out.registers (adderReg 9) = rest ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 5 * multiplicand.length + 4 := by
  have hsetup := binaryStackMultiplierProgram_true_setup O bits c acc multiplicand rest
    hout hcontrol hacc hmult htemp hmarker hden hcounter
  rcases hsetup with ⟨hctl₀, h6₀, h5₀, h4₀, h3₀, h7₀, h9₀, h8₀, hout₀, hcalls₀, hcost₀⟩
  let c₀ := execution binaryStackMultiplierProgram O c bits 2
  have hcopy := binaryStackMultiplierProgram_copy O
    (fun t => bits (2 + t)) c₀ multiplicand [] hout₀ hctl₀ h5₀ h4₀ h7₀
  rcases hcopy with ⟨hctl₁, h4₁, h5₁, h7₁, h3₁, h6₁, h8₁, h9₁,
    hout₁, hcalls₁, hcost₁⟩
  have htotal : 5 * multiplicand.length + 4 = 2 + (5 * multiplicand.length + 2) := by omega
  have hrun := execution_append binaryStackMultiplierProgram O c bits 2
    (5 * multiplicand.length + 2)
  rw [← htotal] at hrun
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * multiplicand.length + 4)).control = _
    rw [hrun]
    simpa [c₀] using hctl₁
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * multiplicand.length + 4)).registers (adderReg 3) = _
    rw [hrun]
    calc
      (execution binaryStackMultiplierProgram O c₀ (fun t => bits (2 + t))
        (5 * multiplicand.length + 2)).registers (adderReg 3) =
          c₀.registers (adderReg 3) := by simpa [List.length_reverse] using h3₁
      _ = [] := by simpa [c₀] using h3₀
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * multiplicand.length + 4)).registers (adderReg 4) = _
    rw [hrun]
    exact h4₁
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * multiplicand.length + 4)).registers (adderReg 5) = _
    rw [hrun]
    simpa [c₀, List.reverse_reverse] using h5₁
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * multiplicand.length + 4)).registers (adderReg 6) = _
    rw [hrun]
    calc
      (execution binaryStackMultiplierProgram O c₀ (fun t => bits (2 + t))
        (5 * multiplicand.length + 2)).registers (adderReg 6) =
          c₀.registers (adderReg 6) := by simpa [List.length_reverse] using h6₁
      _ = acc := by simpa [c₀] using h6₀
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * multiplicand.length + 4)).registers (adderReg 7) = _
    rw [hrun]
    simpa [c₀, List.reverse_reverse] using h7₁
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * multiplicand.length + 4)).registers (adderReg 8) = _
    rw [hrun]
    calc
      (execution binaryStackMultiplierProgram O c₀ (fun t => bits (2 + t))
        (5 * multiplicand.length + 2)).registers (adderReg 8) =
          c₀.registers (adderReg 8) := by simpa [List.length_reverse] using h8₁
      _ = [] := by simpa [c₀] using h8₀.trans hscratch
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * multiplicand.length + 4)).registers (adderReg 9) = _
    rw [hrun]
    calc
      (execution binaryStackMultiplierProgram O c₀ (fun t => bits (2 + t))
        (5 * multiplicand.length + 2)).registers (adderReg 9) =
          c₀.registers (adderReg 9) := by simpa [List.length_reverse] using h9₁
      _ = rest := by simpa [c₀] using h9₀
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * multiplicand.length + 4)).output = none
    rw [hrun]
    exact hout₁
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * multiplicand.length + 4)).oracleCalls = c.oracleCalls
    rw [hrun]
    calc
      (execution binaryStackMultiplierProgram O c₀ (fun t => bits (2 + t))
        (5 * multiplicand.length + 2)).oracleCalls = c₀.oracleCalls := hcalls₁
      _ = c.oracleCalls := by simpa [c₀] using hcalls₀
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * multiplicand.length + 4)).bitOperations = _
    rw [hrun]
    calc
      (execution binaryStackMultiplierProgram O c₀ (fun t => bits (2 + t))
        (5 * multiplicand.length + 2)).bitOperations =
          c₀.bitOperations + (5 * multiplicand.length + 2) := by
        simpa [List.length_reverse, Nat.add_assoc] using hcost₁
      _ = c.bitOperations + 2 + (5 * multiplicand.length + 2) := by
        rw [show c₀.bitOperations = c.bitOperations + 2 by simpa [c₀] using hcost₀]
      _ = c.bitOperations + 5 * multiplicand.length + 4 := by omega

/-- Push the adder-return marker and enter the adder's initial control state. -/
theorem binaryStackMultiplierProgram_true_call_entry
    {n : ℕ} (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 37) (acc multiplicand rest : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = ⟨31, by omega⟩)
    (hmarker : c.registers (adderReg 3) = [])
    (htemp : c.registers (adderReg 4) = [])
    (hmult : c.registers (adderReg 5) = multiplicand)
    (hacc : c.registers (adderReg 6) = acc)
    (hden : c.registers (adderReg 7) = multiplicand)
    (hscratch : c.registers (adderReg 8) = [])
    (hcounter : c.registers (adderReg 9) = rest) :
    let out := execution binaryStackMultiplierProgram O c bits 1
    out.control = ⟨0, by omega⟩ ∧
    out.registers (adderReg 3) = [true] ∧
    out.registers (adderReg 4) = [] ∧
    out.registers (adderReg 5) = multiplicand ∧
    out.registers (adderReg 6) = acc ∧
    out.registers (adderReg 7) = multiplicand ∧
    out.registers (adderReg 8) = [] ∧
    out.registers (adderReg 9) = rest ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 1 := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  simp only at hout hcontrol hmarker htemp hmult hacc hden hscratch hcounter
  subst control
  subst output
  simp [adderReg] at hmarker htemp hmult hacc hden hscratch hcounter
  simp [execution, machineStep, binaryStackMultiplierProgram,
    binaryStackAdderWithCall, binaryMultiplierContinuation,
    adderCallInstruction, adderCallTarget, adderReg,
    hmarker, htemp, hmult, hacc, hden, hscratch, hcounter, Function.update]

/-- After the adder returns, consume its marker and shift the multiplicand
left once, returning to the multiplier-bit loop. -/
theorem binaryStackMultiplierProgram_true_return_shift
    {n : ℕ} (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 37) (acc multiplicand rest : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = ⟨23, by omega⟩)
    (hmarker : c.registers (adderReg 3) = [true])
    (htemp : c.registers (adderReg 4) = [])
    (hmult : c.registers (adderReg 5) = multiplicand)
    (hacc : c.registers (adderReg 6) = acc)
    (hden : c.registers (adderReg 7) = [true])
    (hscratch : c.registers (adderReg 8) = [])
    (hcounter : c.registers (adderReg 9) = rest) :
    let out := execution binaryStackMultiplierProgram O c bits 2
    out.control = ⟨25, by omega⟩ ∧
    out.registers (adderReg 3) = [] ∧
    out.registers (adderReg 4) = [] ∧
    out.registers (adderReg 5) = false :: multiplicand ∧
    out.registers (adderReg 6) = acc ∧
    out.registers (adderReg 7) = [true] ∧
    out.registers (adderReg 8) = [] ∧
    out.registers (adderReg 9) = rest ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 2 := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  simp only at hout hcontrol hmarker htemp hmult hacc hden hscratch hcounter
  subst control
  subst output
  simp [adderReg] at hmarker htemp hmult hacc hden hscratch hcounter
  simp [execution, machineStep, binaryStackMultiplierProgram,
    binaryStackAdderWithCall, binaryMultiplierContinuation,
    adderCallInstruction, adderCallTarget, adderReg,
    hmarker, htemp, hmult, hacc, hden, hscratch, hcounter, Function.update]

/-- One complete true-bit transition: prepare the copied operand, call the
verified adder, shift the multiplicand, and return to the multiplier loop. -/
theorem binaryStackMultiplierProgram_true_bit
    {n : ℕ} (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 37) (acc multiplicand rest : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = ⟨25, by omega⟩)
    (hacc : c.registers (adderReg 6) = acc)
    (hmult : c.registers (adderReg 5) = multiplicand)
    (htemp : c.registers (adderReg 4) = [])
    (hmarker : c.registers (adderReg 3) = [])
    (hden : c.registers (adderReg 7) = [true])
    (hscratch : c.registers (adderReg 8) = [])
    (hcounter : c.registers (adderReg 9) = true :: rest) :
    let steps := 5 * multiplicand.length + adderTotalSteps acc multiplicand + 8
    let out := execution binaryStackMultiplierProgram O c bits steps
    out.control = ⟨25, by omega⟩ ∧
    out.registers (adderReg 3) = [] ∧
    out.registers (adderReg 4) = [] ∧
    out.registers (adderReg 5) = false :: multiplicand ∧
    out.registers (adderReg 6) = addBitsAux false acc multiplicand ∧
    out.registers (adderReg 7) = [true] ∧
    out.registers (adderReg 8) = [] ∧
    out.registers (adderReg 9) = rest ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 5 * multiplicand.length +
      3 * max acc.length multiplicand.length + adderCarrySteps acc multiplicand +
      2 * (adderFinalScratch acc multiplicand).length + 11 := by
  let prepareSteps := 5 * multiplicand.length + 4
  let adderSteps := adderTotalSteps acc multiplicand + 1
  let finishSteps := 2
  have hready := binaryStackMultiplierProgram_true_ready O bits c acc multiplicand rest
    hout hcontrol hacc hmult htemp hmarker hden hscratch hcounter
  rcases hready with ⟨hctl₁, h3₁, h4₁, h5₁, h6₁, h7₁, h8₁, h9₁,
    hout₁, hcalls₁, hcost₁⟩
  let c₁ := execution binaryStackMultiplierProgram O c bits prepareSteps
  have hentry := binaryStackMultiplierProgram_true_call_entry O
    (fun t => bits (prepareSteps + t)) c₁ acc multiplicand rest
    hout₁ hctl₁ h3₁ h4₁ h5₁ h6₁ h7₁ h8₁ h9₁
  rcases hentry with ⟨hctl₂, h3₂, h4₂, h5₂, h6₂, h7₂, h8₂, h9₂,
    hout₂, hcalls₂, hcost₂⟩
  let c₂ := execution binaryStackMultiplierProgram O c₁
    (fun t => bits (prepareSteps + t)) 1
  have hadd := binaryStackAdderWithCall_correct binaryMultiplierContinuation
    ⟨1, by omega⟩ O (fun t => bits (prepareSteps + 1 + t)) c₂ acc multiplicand
    hout₂ (by simpa [c₂, binaryStackMultiplierProgram, binaryStackAdderWithCall,
      adderWideState, adderState] using hctl₂)
    h6₂ h7₂ h8₂
  rcases hadd with ⟨hctl₃, h6₃, h7₃, h8₃, h9₃, h3₃, h4₃, h5₃,
    hout₃, hcalls₃, hcost₃⟩
  let c₃ := execution (binaryStackAdderWithCall binaryMultiplierContinuation ⟨1, by omega⟩)
    O c₂ (fun t => bits (prepareSteps + 1 + t)) adderSteps
  have hc3 : c₃ = execution binaryStackMultiplierProgram O c₂
      (fun t => bits (prepareSteps + 1 + t)) adderSteps := by
    simp [c₃, binaryStackMultiplierProgram]
  have h3entry : c₂.registers (adderReg 3) = [true] := by
    simpa [c₂] using h3₂
  have h3out : c₃.registers (adderReg 3) = [true] := by
    calc
      c₃.registers (adderReg 3) = c₂.registers (adderReg 3) := by
        simpa [hc3, adderSteps, binaryStackMultiplierProgram] using h3₃
      _ = [true] := h3entry
  have h4out : c₃.registers (adderReg 4) = [] := by
    calc
      c₃.registers (adderReg 4) = c₂.registers (adderReg 4) := by
        simpa [hc3, adderSteps, binaryStackMultiplierProgram] using h4₃
      _ = [] := by simpa [c₂] using h4₂
  have h5out : c₃.registers (adderReg 5) = multiplicand := by
    calc
      c₃.registers (adderReg 5) = c₂.registers (adderReg 5) := by
        simpa [hc3, adderSteps, binaryStackMultiplierProgram] using h5₃
      _ = multiplicand := by simpa [c₂] using h5₂
  have h6out : c₃.registers (adderReg 6) = addBitsAux false acc multiplicand := by
    simpa [hc3, adderSteps, binaryStackMultiplierProgram] using h6₃
  have h7out : c₃.registers (adderReg 7) = [true] := by
    simpa [hc3, adderSteps, binaryStackMultiplierProgram] using h7₃
  have h8out : c₃.registers (adderReg 8) = [] := by
    simpa [hc3, adderSteps, binaryStackMultiplierProgram] using h8₃
  have h9out : c₃.registers (adderReg 9) = rest := by
    calc
      c₃.registers (adderReg 9) = c₂.registers (adderReg 9) := by
        simpa [hc3, adderSteps, binaryStackMultiplierProgram] using h9₃
      _ = rest := by simpa [c₂] using h9₂
  have hctl3' : c₃.control = ⟨23, by omega⟩ := by
    simpa [hc3, adderSteps, binaryStackMultiplierProgram] using hctl₃
  have hout3' : c₃.output = none := by
    simpa [hc3, adderSteps, binaryStackMultiplierProgram] using hout₃
  have haddcalls' : c₃.oracleCalls = c₂.oracleCalls := by
    simpa [hc3, adderSteps, binaryStackMultiplierProgram] using hcalls₃
  have haddcost' : c₃.bitOperations = c₂.bitOperations + adderSteps := by
    simpa [hc3, adderSteps, binaryStackMultiplierProgram, adderTotalSteps,
      adderCarrySteps, adderFinalScratch, Nat.add_assoc] using hcost₃
  have hfinish := binaryStackMultiplierProgram_true_return_shift O
    (fun t => bits (prepareSteps + 1 + adderSteps + t)) c₃
    (addBitsAux false acc multiplicand) multiplicand rest
    hout3' hctl3' h3out h4out h5out h6out h7out h8out h9out
  rcases hfinish with ⟨hctl₄, h3₄, h4₄, h5₄, h6₄, h7₄, h8₄, h9₄,
    hout₄, hcalls₄, hcost₄⟩
  let c₄ := execution binaryStackMultiplierProgram O c₃
    (fun t => bits (prepareSteps + 1 + adderSteps + t)) finishSteps
  have htotal : 5 * multiplicand.length + adderTotalSteps acc multiplicand + 8 =
      prepareSteps + (1 + (adderSteps + finishSteps)) := by
    dsimp [prepareSteps, adderSteps, finishSteps]
    omega
  have hcompose := execution_append_three binaryStackMultiplierProgram O c bits
    prepareSteps 1 (adderSteps + finishSteps)
  have hsplit := execution_append
    (binaryStackAdderWithCall binaryMultiplierContinuation ⟨1, by omega⟩) O c₂
    (fun t => bits (prepareSteps + 1 + t)) adderSteps finishSteps
  have hsplit' : execution binaryStackMultiplierProgram O c₂
      (fun t => bits (prepareSteps + 1 + t)) (adderSteps + finishSteps) =
    execution binaryStackMultiplierProgram O
      (execution binaryStackMultiplierProgram O c₂
        (fun t => bits (prepareSteps + 1 + t)) adderSteps)
      (fun t => bits (prepareSteps + 1 + (adderSteps + t))) finishSteps := by
    simpa [binaryStackMultiplierProgram] using hsplit
  have htape : (fun t => bits (prepareSteps + 1 + (adderSteps + t))) =
      (fun t => bits (prepareSteps + 1 + adderSteps + t)) := by
    funext t
    congr 1
    omega
  have hrun : execution binaryStackMultiplierProgram O c bits
      (5 * multiplicand.length + adderTotalSteps acc multiplicand + 8) = c₄ := by
    rw [htotal, hcompose, hsplit']
    simpa [c₁, c₂, c₃, c₄, prepareSteps, adderSteps, finishSteps,
      binaryStackMultiplierProgram, htape]
  have hcost₁' : c₁.bitOperations = c.bitOperations + prepareSteps := by
    simpa [c₁, prepareSteps, Nat.add_assoc] using hcost₁
  have hcost₂' : c₂.bitOperations = c₁.bitOperations + 1 := by
    simpa [c₂] using hcost₂
  have hcalls₁' : c₁.oracleCalls = c.oracleCalls := by
    simpa [c₁, prepareSteps] using hcalls₁
  have hcalls₂' : c₂.oracleCalls = c₁.oracleCalls := by
    simpa [c₂] using hcalls₂
  have hcost₃' : c₃.bitOperations = c₂.bitOperations + adderSteps := by
    exact haddcost'
  have hcalls₃' : c₃.oracleCalls = c₂.oracleCalls := by
    exact haddcalls'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * multiplicand.length + adderTotalSteps acc multiplicand + 8)).control = _
    rw [hrun]
    exact hctl₄
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * multiplicand.length + adderTotalSteps acc multiplicand + 8)).registers
      (adderReg 3) = _
    rw [hrun]
    exact h3₄
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * multiplicand.length + adderTotalSteps acc multiplicand + 8)).registers
      (adderReg 4) = _
    rw [hrun]
    exact h4₄
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * multiplicand.length + adderTotalSteps acc multiplicand + 8)).registers
      (adderReg 5) = _
    rw [hrun]
    exact h5₄
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * multiplicand.length + adderTotalSteps acc multiplicand + 8)).registers
      (adderReg 6) = _
    rw [hrun]
    exact h6₄
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * multiplicand.length + adderTotalSteps acc multiplicand + 8)).registers
      (adderReg 7) = _
    rw [hrun]
    exact h7₄
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * multiplicand.length + adderTotalSteps acc multiplicand + 8)).registers
      (adderReg 8) = _
    rw [hrun]
    exact h8₄
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * multiplicand.length + adderTotalSteps acc multiplicand + 8)).registers
      (adderReg 9) = _
    rw [hrun]
    exact h9₄
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * multiplicand.length + adderTotalSteps acc multiplicand + 8)).output = none
    rw [hrun]
    exact hout₄
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * multiplicand.length + adderTotalSteps acc multiplicand + 8)).oracleCalls =
        c.oracleCalls
    rw [hrun]
    calc
      c₄.oracleCalls = c₃.oracleCalls := hcalls₄
      _ = c₂.oracleCalls := hcalls₃'
      _ = c₁.oracleCalls := hcalls₂'
      _ = c.oracleCalls := hcalls₁'
  · change (execution binaryStackMultiplierProgram O c bits
      (5 * multiplicand.length + adderTotalSteps acc multiplicand + 8)).bitOperations = _
    rw [hrun]
    have hcost4' : c₄.bitOperations = c₃.bitOperations + finishSteps := by
      simpa [c₄, finishSteps] using hcost₄
    rw [hcost4', hcost₃', hcost₂', hcost₁']
    rw [show adderSteps = 3 * max acc.length multiplicand.length +
      adderCarrySteps acc multiplicand + 2 * (adderFinalScratch acc multiplicand).length + 4 by
        dsimp [adderSteps, adderTotalSteps, adderCarrySteps]
      ]
    dsimp [prepareSteps, finishSteps]
    omega

/-- With no multiplier bits left, the loop enters its final halt and returns
the accumulated integer over the fixed denominator one. -/
theorem binaryStackMultiplierProgram_terminal
    {n : ℕ} (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 37) (acc multiplicand : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = ⟨25, by omega⟩)
    (hacc : c.registers (adderReg 6) = acc)
    (hmult : c.registers (adderReg 5) = multiplicand)
    (htemp : c.registers (adderReg 4) = [])
    (hmarker : c.registers (adderReg 3) = [])
    (hden : c.registers (adderReg 7) = [true])
    (hscratch : c.registers (adderReg 8) = [])
    (hcounter : c.registers (adderReg 9) = []) :
    let out := execution binaryStackMultiplierProgram O c bits 2
    out.control = ⟨36, by omega⟩ ∧
    out.output = some ((binaryValue acc : ℚ) / 1) ∧
    out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + acc.length + 3 := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  simp only at hout hcontrol hacc hmult htemp hmarker hden hscratch hcounter
  subst control
  subst output
  simp [adderReg] at hacc hmult htemp hmarker hden hscratch hcounter
  simp [execution, machineStep, binaryStackMultiplierProgram,
    binaryStackAdderWithCall, binaryMultiplierContinuation,
    adderCallInstruction, adderCallTarget, adderReg,
    hacc, hmult, htemp, hmarker, hden, hscratch, hcounter,
    binaryValue, Function.update] <;> omega

/-- The shift-and-add multiplier loop halts with exactly the arithmetic
specified by `binaryStackMultiplierResultBits`; this also records its exact
oracle-call and bit-operation behavior. -/
theorem binaryStackMultiplierProgram_loop_correct
    {n : ℕ} (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 37) (acc multiplicand multiplier : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = ⟨25, by omega⟩)
    (hacc : c.registers (adderReg 6) = acc)
    (hmult : c.registers (adderReg 5) = multiplicand)
    (htemp : c.registers (adderReg 4) = [])
    (hmarker : c.registers (adderReg 3) = [])
    (hden : c.registers (adderReg 7) = [true])
    (hscratch : c.registers (adderReg 8) = [])
    (hcounter : c.registers (adderReg 9) = multiplier) :
    let out := execution binaryStackMultiplierProgram O c bits
      (binaryStackMultiplierLoopSteps acc multiplicand multiplier)
    out.control = ⟨36, by omega⟩ ∧
    out.output = some ((binaryValue
      (binaryStackMultiplierResultBits acc multiplicand multiplier) : ℚ) / 1) ∧
    out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations +
      binaryStackMultiplierLoopBitOperations acc multiplicand multiplier := by
  induction multiplier generalizing acc multiplicand c bits with
  | nil =>
      have hterm := binaryStackMultiplierProgram_terminal O bits c acc multiplicand
        hout hcontrol hacc hmult htemp hmarker hden hscratch hcounter
      rcases hterm with ⟨hctl, hout', hcalls, hcost⟩
      simpa [binaryStackMultiplierLoopSteps, binaryStackMultiplierLoopBitOperations,
        binaryStackMultiplierResultBits, Nat.add_assoc] using And.intro hctl
          (And.intro hout' (And.intro hcalls (by simpa [Nat.add_assoc] using hcost)))
  | cons bit rest ih =>
      cases bit
      · have hstep := binaryStackMultiplierProgram_zero_bit O bits c acc multiplicand rest
          hout hcontrol hacc hmult hcounter
        rcases hstep with ⟨hctl₁, h6₁, h5₁, h9₁, h3₁, h4₁, h7₁, h8₁,
          hout₁, hcalls₁, hcost₁⟩
        let c₁ := execution binaryStackMultiplierProgram O c bits 2
        have h3₁' : c₁.registers (adderReg 3) = [] := by
          simpa [c₁] using h3₁.trans hmarker
        have h4₁' : c₁.registers (adderReg 4) = [] := by
          simpa [c₁] using h4₁.trans htemp
        have h7₁' : c₁.registers (adderReg 7) = [true] := by
          simpa [c₁] using h7₁.trans hden
        have h8₁' : c₁.registers (adderReg 8) = [] := by
          simpa [c₁] using h8₁.trans hscratch
        have htail := ih (acc := acc) (multiplicand := false :: multiplicand)
          (c := c₁) (bits := fun t => bits (2 + t))
          hout₁ hctl₁ h6₁ h5₁ h4₁' h3₁' h7₁' h8₁' h9₁
        rcases htail with ⟨hctl₂, hout₂, hcalls₂, hcost₂⟩
        have htotal : binaryStackMultiplierLoopSteps acc multiplicand (false :: rest) =
            2 + binaryStackMultiplierLoopSteps acc (false :: multiplicand) rest := by
          simp [binaryStackMultiplierLoopSteps, binaryStackMultiplierResultBits]
        have hrun := execution_append binaryStackMultiplierProgram O c bits 2
          (binaryStackMultiplierLoopSteps acc (false :: multiplicand) rest)
        rw [← htotal] at hrun
        have hcalls₁' : c₁.oracleCalls = c.oracleCalls := by
          simpa [c₁] using hcalls₁
        have hcost₁' : c₁.bitOperations = c.bitOperations + 2 := by
          simpa [c₁] using hcost₁
        refine ⟨?_, ?_, ?_, ?_⟩
        · change (execution binaryStackMultiplierProgram O c bits
            (binaryStackMultiplierLoopSteps acc multiplicand (false :: rest))).control = _
          rw [hrun]
          exact hctl₂
        · change (execution binaryStackMultiplierProgram O c bits
            (binaryStackMultiplierLoopSteps acc multiplicand (false :: rest))).output = _
          rw [hrun]
          simpa [binaryStackMultiplierResultBits] using hout₂
        · change (execution binaryStackMultiplierProgram O c bits
            (binaryStackMultiplierLoopSteps acc multiplicand (false :: rest))).oracleCalls = _
          rw [hrun]
          calc
            (execution binaryStackMultiplierProgram O c₁
              (fun t => bits (2 + t))
              (binaryStackMultiplierLoopSteps acc (false :: multiplicand) rest)).oracleCalls =
                c₁.oracleCalls := hcalls₂
            _ = c.oracleCalls := hcalls₁'
        · change (execution binaryStackMultiplierProgram O c bits
            (binaryStackMultiplierLoopSteps acc multiplicand (false :: rest))).bitOperations = _
          rw [hrun, hcost₂]
          rw [hcost₁']
          simp [binaryStackMultiplierLoopBitOperations] <;> omega
      · have hstep := binaryStackMultiplierProgram_true_bit O bits c acc multiplicand rest
          hout hcontrol hacc hmult htemp hmarker hden hscratch hcounter
        rcases hstep with ⟨hctl₁, h3₁, h4₁, h5₁, h6₁, h7₁, h8₁, h9₁,
          hout₁, hcalls₁, hcost₁⟩
        let step := 5 * multiplicand.length + adderTotalSteps acc multiplicand + 8
        let c₁ := execution binaryStackMultiplierProgram O c bits step
        have htail := ih (acc := addBitsAux false acc multiplicand)
          (multiplicand := false :: multiplicand) (c := c₁)
          (bits := fun t => bits (step + t))
          hout₁ hctl₁ h6₁ h5₁ h4₁ h3₁ h7₁ h8₁ h9₁
        rcases htail with ⟨hctl₂, hout₂, hcalls₂, hcost₂⟩
        have htotal : binaryStackMultiplierLoopSteps acc multiplicand (true :: rest) =
            step + binaryStackMultiplierLoopSteps
              (addBitsAux false acc multiplicand) (false :: multiplicand) rest := by
          simp [binaryStackMultiplierLoopSteps, step]
        have hrun := execution_append binaryStackMultiplierProgram O c bits step
          (binaryStackMultiplierLoopSteps (addBitsAux false acc multiplicand)
            (false :: multiplicand) rest)
        rw [← htotal] at hrun
        have hcalls₁' : c₁.oracleCalls = c.oracleCalls := by
          simpa [c₁, step] using hcalls₁
        have hcost₁' : c₁.bitOperations = c.bitOperations + step := by
          calc
            c₁.bitOperations = c.bitOperations + 5 * multiplicand.length +
                3 * max acc.length multiplicand.length + adderCarrySteps acc multiplicand +
                2 * (adderFinalScratch acc multiplicand).length + 11 := by
              simpa [c₁, step] using hcost₁
            _ = c.bitOperations + step := by
              dsimp [step, adderTotalSteps, adderCarrySteps]
              omega
        have hstepCost : step = 5 * multiplicand.length +
            3 * max acc.length multiplicand.length + adderCarrySteps acc multiplicand +
            2 * (adderFinalScratch acc multiplicand).length + 11 := by
          dsimp [step, adderTotalSteps]
          omega
        refine ⟨?_, ?_, ?_, ?_⟩
        · change (execution binaryStackMultiplierProgram O c bits
            (binaryStackMultiplierLoopSteps acc multiplicand (true :: rest))).control = _
          rw [hrun]
          exact hctl₂
        · change (execution binaryStackMultiplierProgram O c bits
            (binaryStackMultiplierLoopSteps acc multiplicand (true :: rest))).output = _
          rw [hrun]
          simpa [binaryStackMultiplierResultBits] using hout₂
        · change (execution binaryStackMultiplierProgram O c bits
            (binaryStackMultiplierLoopSteps acc multiplicand (true :: rest))).oracleCalls = _
          rw [hrun]
          calc
            (execution binaryStackMultiplierProgram O c₁ (fun t => bits (step + t))
              (binaryStackMultiplierLoopSteps (addBitsAux false acc multiplicand)
                (false :: multiplicand) rest)).oracleCalls = c₁.oracleCalls := hcalls₂
            _ = c.oracleCalls := hcalls₁'
        · change (execution binaryStackMultiplierProgram O c bits
            (binaryStackMultiplierLoopSteps acc multiplicand (true :: rest))).bitOperations = _
          rw [hrun, hcost₂]
          rw [hcost₁']
          rw [hstepCost]
          simp [binaryStackMultiplierLoopBitOperations, Nat.add_assoc] <;> omega

/-- The whole binary multiplier loop has a quadratic bit-operation bound in
the initial operand widths and multiplier length. -/
theorem binaryStackMultiplierLoopBitOperations_le_quadratic
    (acc multiplicand multiplier : List Bool) :
    binaryStackMultiplierLoopBitOperations acc multiplicand multiplier ≤
      100 * (multiplier.length + 1) *
        (max acc.length multiplicand.length + multiplier.length + 5) := by
  induction multiplier generalizing acc multiplicand with
  | nil => simp [binaryStackMultiplierLoopBitOperations] <;> omega
  | cons bit rest ih =>
      let width := max acc.length multiplicand.length + rest.length + 6
      have haux := embedded_addBitsAux_length_le false acc multiplicand
      have hnewwidth :
          max (if bit then (addBitsAux false acc multiplicand).length else acc.length)
            (multiplicand.length + 1) + rest.length + 5 ≤ width := by
        dsimp [width]
        have hnew : (addBitsAux false acc multiplicand).length ≤
            max acc.length multiplicand.length + 1 := haux
        have ha : acc.length ≤ max acc.length multiplicand.length := le_max_left _ _
        have hm : multiplicand.length ≤ max acc.length multiplicand.length := le_max_right _ _
        have hm' : multiplicand.length + 1 ≤ max acc.length multiplicand.length + 1 := by omega
        cases bit
        ·
          have hmax : max acc.length (multiplicand.length + 1) ≤
              max acc.length multiplicand.length + 1 := max_le (by omega) hm'
          calc
            max acc.length (multiplicand.length + 1) + rest.length + 5 ≤
                (max acc.length multiplicand.length + 1) + rest.length + 5 := by
              simpa using Nat.add_le_add_right hmax (rest.length + 5)
            _ = max acc.length multiplicand.length + rest.length + 6 := by omega
        ·
          have hmax : max (addBitsAux false acc multiplicand).length
              (multiplicand.length + 1) ≤ max acc.length multiplicand.length + 1 :=
            max_le hnew hm'
          calc
            max (addBitsAux false acc multiplicand).length (multiplicand.length + 1) +
                rest.length + 5 ≤
                (max acc.length multiplicand.length + 1) + rest.length + 5 := by
              simpa using Nat.add_le_add_right hmax (rest.length + 5)
            _ = max acc.length multiplicand.length + rest.length + 6 := by omega
      have htail := ih
        (acc := if bit then addBitsAux false acc multiplicand else acc)
        (multiplicand := false :: multiplicand)
      have htail' :
          binaryStackMultiplierLoopBitOperations
              (if bit then addBitsAux false acc multiplicand else acc)
              (false :: multiplicand) rest ≤
            100 * (rest.length + 1) * width := by
        calc
          _ ≤ 100 * (rest.length + 1) *
              (max (if bit then (addBitsAux false acc multiplicand).length else acc.length)
                (false :: multiplicand).length + rest.length + 5) := by
                cases bit <;> simpa [List.length_cons] using htail
          _ ≤ 100 * (rest.length + 1) * width := by
                exact Nat.mul_le_mul_left (100 * (rest.length + 1)) hnewwidth
      have hcarry : adderCarrySteps acc multiplicand ≤ 3 := by
        by_cases h : (addBitsPass false acc multiplicand).2 <;>
          simp [adderCarrySteps, h]
      have hscratch := embedded_adderFinalScratch_length_le acc multiplicand
      have hfirst :
          (if bit then 5 * multiplicand.length +
            3 * max acc.length multiplicand.length + adderCarrySteps acc multiplicand +
            2 * (adderFinalScratch acc multiplicand).length + 11 else 2) ≤
            100 * width := by
        cases bit <;> dsimp [width] <;> omega
      simp only [binaryStackMultiplierLoopBitOperations, List.length_cons]
      calc
        (if bit then 5 * multiplicand.length +
            3 * max acc.length multiplicand.length + adderCarrySteps acc multiplicand +
            2 * (adderFinalScratch acc multiplicand).length + 11 else 2) +
            binaryStackMultiplierLoopBitOperations
              (if bit then addBitsAux false acc multiplicand else acc)
              (false :: multiplicand) rest ≤
            100 * width + 100 * (rest.length + 1) * width :=
              Nat.add_le_add hfirst htail'
        _ = 100 * (rest.length + 2) * width := by ring
        _ = 100 * ((rest.length + 1) + 1) *
            (max acc.length multiplicand.length + (rest.length + 1) + 5) := by
              dsimp [width]
              ring

/-- Specializing the loop to a zero initial accumulator realizes natural
multiplication on the little-endian operand stacks. -/
theorem binaryStackMultiplierProgram_loop_product_output
    {n : ℕ} (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 37) (multiplicand multiplier : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = ⟨25, by omega⟩)
    (hacc : c.registers (adderReg 6) = [])
    (hmult : c.registers (adderReg 5) = multiplicand)
    (htemp : c.registers (adderReg 4) = [])
    (hmarker : c.registers (adderReg 3) = [])
    (hden : c.registers (adderReg 7) = [true])
    (hscratch : c.registers (adderReg 8) = [])
    (hcounter : c.registers (adderReg 9) = multiplier) :
    let out := execution binaryStackMultiplierProgram O c bits
      (binaryStackMultiplierLoopSteps [] multiplicand multiplier)
    out.output = some ((binaryValue multiplicand : ℚ) * binaryValue multiplier) := by
  have hloop := binaryStackMultiplierProgram_loop_correct O bits c [] multiplicand multiplier
    hout hcontrol hacc hmult htemp hmarker hden hscratch hcounter
  rcases hloop with ⟨_, hout', _, _⟩
  have hvalue : binaryValue (binaryStackMultiplierResultBits [] multiplicand multiplier) =
      binaryValue multiplicand * binaryValue multiplier := by
    simpa [binaryValue] using
      binaryValue_binaryStackMultiplierResultBits [] multiplicand multiplier
  change (execution binaryStackMultiplierProgram O c bits
    (binaryStackMultiplierLoopSteps [] multiplicand multiplier)).output = _
  rw [hout']
  simp [hvalue]

theorem binaryStackMultiplierLoopSteps_le_bitOperations
    (acc multiplicand multiplier : List Bool) :
    binaryStackMultiplierLoopSteps acc multiplicand multiplier ≤
      binaryStackMultiplierLoopBitOperations acc multiplicand multiplier := by
  induction multiplier generalizing acc multiplicand with
  | nil => simp [binaryStackMultiplierLoopSteps, binaryStackMultiplierLoopBitOperations]
  | cons bit rest ih =>
      cases bit
      · have htail := ih (acc := acc) (multiplicand := false :: multiplicand)
        simpa [binaryStackMultiplierLoopSteps, binaryStackMultiplierLoopBitOperations] using
          Nat.add_le_add_left htail 2
      · have htail := ih (acc := addBitsAux false acc multiplicand)
          (multiplicand := false :: multiplicand)
        simp [binaryStackMultiplierLoopSteps, binaryStackMultiplierLoopBitOperations,
          adderTotalSteps, htail, Nat.add_assoc] <;> omega

/-- The fixed multiplier's running time is quadratic in the initial operand
width and multiplier length. -/
theorem binaryStackMultiplierLoopSteps_le_quadratic
    (acc multiplicand multiplier : List Bool) :
    binaryStackMultiplierLoopSteps acc multiplicand multiplier ≤
      100 * (multiplier.length + 1) *
        (max acc.length multiplicand.length + multiplier.length + 5) := by
  exact le_trans (binaryStackMultiplierLoopSteps_le_bitOperations acc multiplicand multiplier)
    (binaryStackMultiplierLoopBitOperations_le_quadratic acc multiplicand multiplier)

end OAI.CommonBasesFPRAS


