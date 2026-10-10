-- Prove2me | solution 1 for ActuarialValuation.gamblerFiniteRuin_zero_capital
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:46:29.952984+00:00
-- url     : https://prove2.me/submissions/48d41631-c049-4b91-9f7e-ba75da3208e0

import Definitions.Def_actuarial_gamblerFiniteRuin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (N n : ℕ) (p : ℝ) :
    gamblerFiniteRuin N p n 0 = 1 := by
  cases n <;> simp [gamblerFiniteRuin]
