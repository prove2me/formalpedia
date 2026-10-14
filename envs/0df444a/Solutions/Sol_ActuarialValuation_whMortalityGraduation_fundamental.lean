-- Prove2me | solution 1 for ActuarialValuation.whMortalityGraduation_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T07:03:00.670429+00:00
-- url     : https://prove2.me/submissions/863147a7-0974-427b-bdcb-3548089e76a0

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_whFitPenalty
import Definitions.Def_actuarial_whSecondRoughness
import Definitions.Def_actuarial_whObjectiveTwo
import Definitions.Def_actuarial_whShiftedCurve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (w g crude : ℕ → ℝ) (n : ℕ) (lambda shift : ℝ) (hw : ∀ i ∈ Finset.range n, 0 ≤ w i) (hl : 0 ≤ lambda) : (0 ≤ whFitPenalty w g crude n) ∧ (0 ≤ whSecondRoughness g n) ∧ (0 ≤ whObjectiveTwo (whFitPenalty w g crude n) (whSecondRoughness g n) lambda) ∧ (whSecondRoughness (fun i => whShiftedCurve g shift i) n = whSecondRoughness g n) := by
  have hfit : 0 ≤ whFitPenalty w g crude n := by
    unfold whFitPenalty
    apply Finset.sum_nonneg
    intro i hi
    have hwi : 0 ≤ w i := hw i hi
    simp only [whWeightedFit, whSquaredResidual, whRateResidual]
    positivity
  have hsmooth : 0 ≤ whSecondRoughness g n := by
    unfold whSecondRoughness
    apply Finset.sum_nonneg
    intro i hi
    exact sq_nonneg (whSecondDifference g i)
  have hshift_diff (i : ℕ) :
      whSecondDifference (fun j => whShiftedCurve g shift j) i =
        whSecondDifference g i := by
    unfold whSecondDifference whFirstDifference whShiftedCurve
    ring
  have hshift :
      whSecondRoughness (fun i => whShiftedCurve g shift i) n =
        whSecondRoughness g n := by
    unfold whSecondRoughness
    apply Finset.sum_congr rfl
    intro i hi
    rw [hshift_diff i]
  refine ⟨hfit, hsmooth, ?_, hshift⟩
  unfold whObjectiveTwo
  exact add_nonneg hfit (mul_nonneg hl hsmooth)
