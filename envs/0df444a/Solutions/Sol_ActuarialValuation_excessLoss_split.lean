-- Prove2me | solution 1 for ActuarialValuation.excessLoss_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:50:27.251828+00:00
-- url     : https://prove2.me/submissions/1ab01f08-5634-4311-a191-5c56c4a79453

import Mathlib
import Definitions.Def_actuarial_cededExcessLoss
import Definitions.Def_actuarial_retainedExcessLoss
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (z a : ℝ) :
    retainedExcessLoss z a + cededExcessLoss z a = z := by
  change min z a + (z - min z a) = z
  ring
