-- Prove2me | solution 1 for ActuarialValuation.retainedExcessLoss_zero_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:50:12.808071+00:00
-- url     : https://prove2.me/submissions/db352b9a-9c47-4c15-a50c-e7038f682294

import Mathlib
import Definitions.Def_actuarial_retainedExcessLoss
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (z : ℝ) (hz : 0 ≤ z) :
    retainedExcessLoss z 0 = 0 := by
  change min z 0 = 0
  exact min_eq_right hz
