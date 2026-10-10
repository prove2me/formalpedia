-- Prove2me | solution 1 for ActuarialValuation.quotaShareContinuousOptimum_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:06:12.736427+00:00
-- url     : https://prove2.me/submissions/5bf229fc-191c-4416-9159-983c4bb99472

import Mathlib.Tactic.Linarith
import Definitions.Def_actuarial_quotaShareContinuousOptimum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (loading capital : ℝ) (hl : 0 ≤ loading)
    (hc : 0 ≤ capital) (hpos : 0 < loading + capital) :
    quotaShareContinuousOptimum loading capital ≤ 1 := by
  dsimp [quotaShareContinuousOptimum]
  apply (div_le_iff₀ hpos).2
  linarith
