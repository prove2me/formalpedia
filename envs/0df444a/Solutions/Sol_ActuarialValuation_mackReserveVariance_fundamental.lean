-- Prove2me | solution 1 for ActuarialValuation.mackReserveVariance_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:40:14.233002+00:00
-- url     : https://prove2.me/submissions/5c55cb09-0e2d-4c5a-bb4b-a469e269286e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackNumerator
import Definitions.Def_actuarial_mackDenominator
import Definitions.Def_actuarial_mackFactor
import Definitions.Def_actuarial_mackProjection
import Definitions.Def_actuarial_mackProcessVariance
import Definitions.Def_actuarial_mackEstimationVariance
import Definitions.Def_actuarial_mackOneStepMSE
import Definitions.Def_actuarial_mackReserve

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c : ℕ → ℕ → ℝ) (m j : ℕ) (hD : 0 < mackDenominator c m j) (current sigma2 : ℝ) (hc : 0 ≤ current) (hs : 0 ≤ sigma2) : (mackFactor c m j * mackDenominator c m j = mackNumerator c m j) ∧ (0 ≤ mackProcessVariance sigma2 current) ∧ (0 ≤ mackEstimationVariance sigma2 current (mackDenominator c m j)) ∧ (0 ≤ mackOneStepMSE (mackProcessVariance sigma2 current) (mackEstimationVariance sigma2 current (mackDenominator c m j))) ∧ (current + mackReserve (mackProjection current (mackFactor c m j)) current = mackProjection current (mackFactor c m j)) := by
  have hfactor : mackFactor c m j * mackDenominator c m j =
      mackNumerator c m j := by
    unfold mackFactor
    field_simp [ne_of_gt hD]
  have hproc : 0 ≤ mackProcessVariance sigma2 current := by
    unfold mackProcessVariance
    exact mul_nonneg hs hc
  have hest : 0 ≤ mackEstimationVariance sigma2 current
      (mackDenominator c m j) := by
    unfold mackEstimationVariance
    exact div_nonneg (mul_nonneg hs (sq_nonneg current)) (le_of_lt hD)
  refine ⟨hfactor, hproc, hest, ?_, ?_⟩
  · unfold mackOneStepMSE
    exact add_nonneg hproc hest
  · unfold mackReserve
    ring
