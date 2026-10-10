-- Prove2me | solution 1 for ActuarialValuation.quotaShareMeanVariance_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:17:29.952927+00:00
-- url     : https://prove2.me/submissions/b8a503d9-dedf-4ac0-b2b8-f2f081743894

import Mathlib
import Definitions.Def_actuarial_quotaShareContinuousOptimum
import Definitions.Def_actuarial_quotaShareCapitalObjective
import Theorems.Thm_ActuarialValuation_quotaShareContinuousOptimum_nonneg
import Theorems.Thm_ActuarialValuation_quotaShareContinuousOptimum_le_one
import Theorems.Thm_ActuarialValuation_quotaShareCapitalObjective_optimal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
    (q claim loading capital : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hl : 0 ≤ loading) (hc : 0 ≤ capital)
    (hpos : 0 < loading + capital) :
    (0 ≤ quotaShareContinuousOptimum loading capital ∧
      quotaShareContinuousOptimum loading capital ≤ 1) ∧
    (∀ retention : ℝ,
      quotaShareCapitalObjective q claim
        (quotaShareContinuousOptimum loading capital) loading capital ≤
      quotaShareCapitalObjective q claim retention loading capital) := by
  refine ⟨⟨quotaShareContinuousOptimum_nonneg loading capital hl hc hpos,
    quotaShareContinuousOptimum_le_one loading capital hl hc hpos⟩, ?_⟩
  intro retention
  exact quotaShareCapitalObjective_optimal
    q claim loading capital retention hq0 hq1 hl hc hpos
