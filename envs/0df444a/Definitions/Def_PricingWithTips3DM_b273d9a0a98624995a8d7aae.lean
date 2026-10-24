-- Prove2me | Definitions.Def_PricingWithTips3DM_b273d9a0a98624995a8d7aae
-- name    : PricingWithTips3DM_b273d9a0a98624995a8d7aae
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T21:15:59.361318+00:00
-- url     : https://prove2.me/theorems/f51bfd50-7b3e-4095-aa1f-c3dd030ca9a2
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Emitter.PolynomialRuntime
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_f820102d1b4254c4f74e0384
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! # General-circuit formula emitter: polynomial-time machine -/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter

open _root_.Turing

def stepBound (inputLength : Nat) : Nat :=
  16 * (inputLength + 1) ^ 2 + 2

theorem guardedReverseSteps_le (guarded : Option Circuit) :
    guardedReverseSteps guarded ≤
      stepBound (encodeGuardedCircuit guarded).length := by
  cases guarded with
  | none => simp [guardedReverseSteps, invalidReverseSteps, stepBound,
      encodeGuardedCircuit]
  | some c =>
      have h := reverseSuccessfulSteps_le c
      simpa [guardedReverseSteps, stepBound, encodeGuardedCircuit] using
        (show reverseSuccessfulSteps c ≤
            16 * ((encodeNormalizedCircuit c).length + 1) ^ 2 + 2 by
          omega)

/-- The reverse-output emitter returns the guarded formula within one uniform
quadratic budget. -/
theorem allGuardedInputsWithinPolynomial (guarded : Option Circuit) :
    Nonempty (TM2OutputsInTime reverseMachine
      (encodeGuardedCircuit guarded)
      (some (guardedCircuitFormulaList guarded).reverse)
      (stepBound (encodeGuardedCircuit guarded).length)) := by
  refine ⟨{
    steps := guardedReverseSteps guarded
    evals_in_steps := guarded_reverse_run guarded
    steps_le_m := guardedReverseSteps_le guarded }⟩

noncomputable def runtimePolynomial : Polynomial Nat :=
  16 * (Polynomial.X + 1) ^ 2 + 2

@[simp] theorem runtimePolynomial_eval (n : Nat) :
    runtimePolynomial.eval n = stepBound n := by
  simp [runtimePolynomial, stepBound, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

/-- Concrete polynomial-time TM2 implementation of guarded circuit formula
emission.  Its list output is reversed so the finite controller can push it
directly; a verified generic reversal removes this implementation detail. -/
noncomputable def reverseComputableInPolyTime :
    TM2ComputableInPolyTime encodeGuardedCircuit id
      (fun guarded => (guardedCircuitFormulaList guarded).reverse) where
  tm := reverseMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := runtimePolynomial
  outputsFun := fun guarded => by
    simpa using Classical.choice (allGuardedInputsWithinPolynomial guarded)

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter


