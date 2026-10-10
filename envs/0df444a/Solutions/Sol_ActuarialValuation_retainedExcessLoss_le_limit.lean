-- Prove2me | solution 1 for ActuarialValuation.retainedExcessLoss_le_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:50:06.348676+00:00
-- url     : https://prove2.me/submissions/cc45a187-e3df-4ed1-a762-d474a83e8d5d

import Mathlib
import Definitions.Def_actuarial_retainedExcessLoss
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (z a : ℝ) :
    retainedExcessLoss z a ≤ a := by
  change min z a ≤ a
  exact min_le_right z a
