-- Prove2me | solution 1 for ActuarialValuation.finiteEntropicRetainedClaim_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:25:26.39287+00:00
-- url     : https://prove2.me/submissions/91954f95-d632-4c2f-8b12-2b34ccfab14a

import Mathlib
import Definitions.Def_actuarial_finiteEntropicRetainedClaim
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution (z a b : ℝ) (hab : a ≤ b) :
    finiteEntropicRetainedClaim z a ≤ finiteEntropicRetainedClaim z b := by
  unfold finiteEntropicRetainedClaim
  exact min_le_min_left z hab
