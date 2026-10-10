-- Prove2me | solution 1 for ActuarialValuation.gamblerFiniteSuccess_zero_capital
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:46:18.575867+00:00
-- url     : https://prove2.me/submissions/a0a8dd4f-13e5-45c0-adf7-d6513a886e64

import Definitions.Def_actuarial_gamblerFiniteSuccess

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (N n : ℕ) (p : ℝ) :
    gamblerFiniteSuccess N p n 0 = 0 := by
  cases n <;> simp [gamblerFiniteSuccess]
