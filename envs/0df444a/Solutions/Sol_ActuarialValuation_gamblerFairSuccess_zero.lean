-- Prove2me | solution 1 for ActuarialValuation.gamblerFairSuccess_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:45:36.114977+00:00
-- url     : https://prove2.me/submissions/a4e3070a-f140-4b57-a34f-07ba51994083

import Definitions.Def_actuarial_gamblerFairSuccess

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (N : ℕ) :
    gamblerFairSuccess N 0 = 0 := by
  simp [gamblerFairSuccess]
