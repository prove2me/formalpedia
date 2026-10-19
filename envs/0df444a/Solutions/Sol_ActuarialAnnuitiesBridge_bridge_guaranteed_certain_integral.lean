-- Prove2me | solution 1 for ActuarialAnnuitiesBridge.bridge_guaranteed_certain_integral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:08:32.170033+00:00
-- url     : https://prove2.me/submissions/f61e6b23-0ca9-42ae-86fb-2b070c8e3002

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bSurvival
import Definitions.Def_actuarial_bcSurvival
import Definitions.Def_actuarial_bcCertainPV


open MeasureTheory

theorem solution (h a g : ℕ) (p : ℕ → ℝ) : ActuarialAnnuitiesContinuous.bcSurvival h p (fun k => (k : ℝ)) (a : ℝ) * ActuarialAnnuitiesContinuous.bcCertainPV (a : ℝ) (g : ℝ) 0 (fun _ => 1) = ActuarialAnnuities.bSurvival h p a * (g : ℝ) := by
  unfold ActuarialAnnuitiesContinuous.bcSurvival ActuarialAnnuitiesContinuous.bcCertainPV
    ActuarialAnnuities.bSurvival ActuarialAnnuitiesContinuous.bcAlive ActuarialAnnuities.bAlive
  simp only [neg_zero, zero_mul, Real.exp_zero, mul_one, intervalIntegral.integral_const, smul_eq_mul]
  congr 1
  · apply Finset.sum_congr rfl; intro k _; simp [Nat.cast_le]
  · ring


