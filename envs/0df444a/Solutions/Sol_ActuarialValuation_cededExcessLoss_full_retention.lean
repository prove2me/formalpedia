-- Prove2me | solution 1 for ActuarialValuation.cededExcessLoss_full_retention
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:50:20.301505+00:00
-- url     : https://prove2.me/submissions/8861725f-f7c8-4510-b779-e1c98e49bce8

import Mathlib
import Definitions.Def_actuarial_cededExcessLoss
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (z a : ℝ) (hza : z ≤ a) :
    cededExcessLoss z a = 0 := by
  change z - min z a = 0
  rw [min_eq_left hza]
  ring
