-- Prove2me | solution 1 for ActuarialValuation.retainedExcessLoss_mono_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:50:34.043723+00:00
-- url     : https://prove2.me/submissions/ebbed01c-9a96-4245-9f86-64f078ba436d

import Mathlib
import Definitions.Def_actuarial_retainedExcessLoss
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (z a b : ℝ) (hab : a ≤ b) :
    retainedExcessLoss z a ≤ retainedExcessLoss z b := by
  change min z a ≤ min z b
  exact min_le_min_left z hab
