-- Prove2me | solution 1 for ActuarialValuation.cm1Discount_multiplicative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:21:33.79843+00:00
-- url     : https://prove2.me/submissions/584df1bd-5560-4636-b605-21fad3d220db

import Mathlib.Tactic
import Definitions.Def_actuarial_cm1Accum
import Definitions.Def_actuarial_cm1Discount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (i : ℝ) (m n : ℕ) : cm1Discount i (m+n) = cm1Discount i m * cm1Discount i n := by
  simp only [cm1Discount, cm1Accum, pow_add, one_div, mul_inv_rev]
  ring
