-- Prove2me | solution 1 for ActuarialValuation.gamblerBiasedSuccess_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:45:56.07998+00:00
-- url     : https://prove2.me/submissions/55f25506-1fe7-4ebd-9a93-a6709f8a946a

import Definitions.Def_actuarial_gamblerBiasedSuccess

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (N : ℕ) (p : ℝ) :
    gamblerBiasedSuccess N 0 p = 0 := by
  simp [gamblerBiasedSuccess]
