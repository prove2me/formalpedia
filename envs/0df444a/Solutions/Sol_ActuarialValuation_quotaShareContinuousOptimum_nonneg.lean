-- Prove2me | solution 1 for ActuarialValuation.quotaShareContinuousOptimum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:06:06.066639+00:00
-- url     : https://prove2.me/submissions/50d137d0-3b9d-4317-8caf-93f356f1cc6e

import Mathlib
import Definitions.Def_actuarial_quotaShareContinuousOptimum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (loading capital : ℝ) (hl : 0 ≤ loading)
    (hc : 0 ≤ capital) (hpos : 0 < loading + capital) :
    0 ≤ quotaShareContinuousOptimum loading capital := by
  dsimp [quotaShareContinuousOptimum]
  exact div_nonneg hl (le_of_lt hpos)
