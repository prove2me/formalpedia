-- Prove2me | solution 1 for ActuarialValuation.retainedExcessLoss_le_claim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:49:59.725754+00:00
-- url     : https://prove2.me/submissions/ef19d905-35a7-4705-9dd3-6a5f709c09ad

import Mathlib
import Definitions.Def_actuarial_retainedExcessLoss
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (z a : ℝ) :
    retainedExcessLoss z a ≤ z := by
  change min z a ≤ z
  exact min_le_left z a
