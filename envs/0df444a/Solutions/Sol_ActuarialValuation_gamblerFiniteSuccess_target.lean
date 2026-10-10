-- Prove2me | solution 1 for ActuarialValuation.gamblerFiniteSuccess_target
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:46:24.281929+00:00
-- url     : https://prove2.me/submissions/31cbcdb1-09a4-4995-82c8-3d757da722a4

import Definitions.Def_actuarial_gamblerFiniteSuccess

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (N n : ℕ) (p : ℝ) (hN : 0 < N) :
    gamblerFiniteSuccess N p n N = 1 := by
  cases n <;> simp [gamblerFiniteSuccess, Nat.ne_of_gt hN]
