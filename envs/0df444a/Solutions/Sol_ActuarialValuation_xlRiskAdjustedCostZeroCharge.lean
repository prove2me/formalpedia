-- Prove2me | solution 1 for ActuarialValuation.xlRiskAdjustedCostZeroCharge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:08:52.763989+00:00
-- url     : https://prove2.me/submissions/185a0f17-b773-44f2-87d8-a500a6b031ab

import Mathlib
import Definitions.Def_actuarial_xlExpectedValuePremiumCost
import Definitions.Def_actuarial_xlRiskAdjustedRetentionCost
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w z : Ω → ℝ) (θ a : ℝ)
  :
  xlRiskAdjustedRetentionCost w z θ 0 a = xlExpectedValuePremiumCost w z a θ := by
  simp [xlRiskAdjustedRetentionCost]
