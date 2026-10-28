-- Prove2me | Definitions.Def_OAICommonBasesFPRASBinaryStackArithmeticSupport
-- name    : OAICommonBasesFPRASBinaryStackArithmeticSupport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T20:27:39.439374+00:00
-- url     : https://prove2.me/theorems/182cd100-1fa2-4d72-8268-840ce9ba8171
-- title:
--   Support lemmas for compositional binary arithmetic
-- statement:
--   Four verified helper lemmas expose the binary-adder carry and return behavior needed to compose the adder as a subroutine.
-- source:
--   Lean 4.33.1 binary-register implementation verified locally; source definitions and proofs are included in the published module.

import Definitions.Def_OAICommonBasesFPRASBinaryStackAdder

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.CommonBasesFPRAS

theorem execution_append {k s n : ℕ} (P : Program k s)
    (O : IndependenceOracle n) (c : MachineConfig k s) (bits : ℕ → Bool)
    (t₀ suffix : ℕ) :
    execution P O c bits (t₀ + suffix) =
      execution P O (execution P O c bits t₀) (fun t => bits (t₀ + t)) suffix := by
  induction suffix with
  | zero => simp [execution]
  | succ suffix ih =>
      calc
        execution P O c bits (t₀ + Nat.succ suffix) =
            machineStep P O (bits (t₀ + suffix))
              (execution P O c bits (t₀ + suffix)) := by rw [Nat.add_succ]; rfl
        _ = machineStep P O (bits (t₀ + suffix))
              (execution P O (execution P O c bits t₀)
                (fun t => bits (t₀ + t)) suffix) := by rw [ih]
        _ = execution P O (execution P O c bits t₀)
              (fun t => bits (t₀ + t)) (Nat.succ suffix) := rfl

end OAI.CommonBasesFPRAS

namespace OAI.CommonBasesFPRAS

/-- One binary full-adder column, with the carry as its third input. -/
theorem addBitsAux_eq_addBitsPass (carry : Bool) (a b : List Bool) :
    addBitsAux carry a b =
      (addBitsPass carry a b).1 ++ (if (addBitsPass carry a b).2 then [true] else []) := by
  induction a generalizing b carry with
  | nil =>
      induction b generalizing carry with
      | nil => cases carry <;> simp [addBitsAux, addBitsPass]
      | cons b bs ih =>
          cases carry <;> cases b <;>
            simp [addBitsAux, addBitsPass, addColumn, ih]
  | cons a as ih =>
      cases b with
      | nil =>
          cases carry <;> cases a <;>
            simp [addBitsAux, addBitsPass, addColumn, ih]
      | cons b bs =>
          cases carry <;> cases a <;> cases b <;>
            simp [addBitsAux, addBitsPass, addColumn, ih]

private theorem binaryValue_addBitsAux_nil (carry : Bool) (b : List Bool) :
    binaryValue (addBitsAux carry [] b) = binaryValue b + carry.toNat := by
  induction b generalizing carry with
  | nil => cases carry <;> simp [addBitsAux, binaryValue]
  | cons b bs ih =>
    cases b <;> cases carry <;> simp [addBitsAux, addColumn, binaryValue, ih] <;> omega

theorem binaryStackAdder_reverseColumn (O : IndependenceOracle 0)
    (bits : ℕ → Bool) (c : MachineConfig 2 21) (bit : Bool)
    (acc rest : List Bool) (hout : c.output = none)
    (hcontrol : c.control = adderState 16)
    (hnum : c.registers (adderReg 6) = acc)
    (hden : c.registers (adderReg 7) = [])
    (hscratch : c.registers (adderReg 8) = bit :: rest) :
    let out := execution binaryStackAdder O c bits 2
    out.control = adderState 16 ∧ out.registers (adderReg 6) = bit :: acc ∧
    out.registers (adderReg 7) = [] ∧ out.registers (adderReg 8) = rest ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 2 := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  simp only at hout hcontrol hnum hden hscratch
  subst control
  subst output
  simp [adderReg] at hnum hden hscratch
  cases bit <;>
    simp [execution, machineStep, binaryStackAdder, adderState, adderReg,
      hnum, hden, hscratch, Function.update]

/-- Reverse the scratch stack and halt, including the machine's output-cost
charge, for any nonempty prefix already accumulated in register 6. -/
theorem execution_append_three {k s n : ℕ} (P : Program k s)
    (O : IndependenceOracle n) (c : MachineConfig k s) (bits : ℕ → Bool)
    (t₁ t₂ t₃ : ℕ) :
    execution P O c bits (t₁ + (t₂ + t₃)) =
      execution P O
        (execution P O (execution P O c bits t₁) (fun t => bits (t₁ + t)) t₂)
        (fun t => bits (t₁ + t₂ + t)) t₃ := by
  rw [execution_append]
  rw [execution_append]
  congr 1
  funext t
  congr 1
  omega

end OAI.CommonBasesFPRAS


