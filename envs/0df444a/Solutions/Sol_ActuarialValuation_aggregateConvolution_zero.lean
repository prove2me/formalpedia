-- Prove2me | solution 1 for ActuarialValuation.aggregateConvolution_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:07:01.483744+00:00
-- url     : https://prove2.me/submissions/82c1b79e-13e3-42b4-9626-0fa20868b7d0

import Mathlib
import Definitions.Def_actuarial_aggregateConvolution
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f g : ℕ → ℝ) :
    aggregateConvolution f g 0 = f 0 * g 0 := by
  simp [aggregateConvolution]
