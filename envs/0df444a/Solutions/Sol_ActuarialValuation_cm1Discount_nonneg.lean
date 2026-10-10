-- Prove2me | solution 1 for ActuarialValuation.cm1Discount_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:24:31.080357+00:00
-- url     : https://prove2.me/submissions/79c7fe29-8043-4ff5-ab66-8ccf63b6b3f8

import Mathlib.Tactic
import Definitions.Def_actuarial_cm1Accum
import Definitions.Def_actuarial_cm1Discount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (i : ℝ) (n : ℕ) (hi : -1 < i) :
    0 < cm1Discount i n := by
  have hp : 0 < 1 + i := by linarith
  change 0 < 1 / (1 + i) ^ n
  exact one_div_pos.mpr (pow_pos hp n)
