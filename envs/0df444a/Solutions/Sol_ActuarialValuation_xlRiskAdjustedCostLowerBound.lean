-- Prove2me | solution 1 for ActuarialValuation.xlRiskAdjustedCostLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:09:01.379989+00:00
-- url     : https://prove2.me/submissions/4a9c547f-5b5f-45b6-ac63-a34794b0f0b3

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_actuarial_xlExpectedValuePremiumCost
import Definitions.Def_actuarial_xlRiskAdjustedRetentionCost
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w z : Ω → ℝ) (θ kap a : ℝ)
  (hw : ∀ ω, 0 ≤ w ω) (hkap : 0 ≤ kap)
  :
  xlExpectedValuePremiumCost w z a θ ≤ xlRiskAdjustedRetentionCost w z θ kap a := by
  classical
  change xlExpectedValuePremiumCost w z a θ ≤
    xlExpectedValuePremiumCost w z a θ + kap * xlRetainedVariance w z a
  have hvariance : 0 ≤ xlRetainedVariance w z a := by
    unfold xlRetainedVariance
    apply Finset.sum_nonneg
    intro ω hω
    exact mul_nonneg (hw ω) (sq_nonneg _)
  exact le_add_of_nonneg_right (mul_nonneg hkap hvariance)
