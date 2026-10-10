-- Prove2me | solution 1 for ActuarialValuation.cm1Discount_accum_cancel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:24:25.18192+00:00
-- url     : https://prove2.me/submissions/d9d261cf-a16c-4624-bb26-bc1d155538ac

import Mathlib.Tactic
import Definitions.Def_actuarial_cm1Accum
import Definitions.Def_actuarial_cm1Discount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (i : ℝ) (n : ℕ) (hi : -1 < i) :
    cm1Discount i n * cm1Accum i n = 1 := by
  have hp : 0 < 1 + i := by linarith
  have hn : (1 + i) ^ n ≠ 0 := ne_of_gt (pow_pos hp n)
  change (1 / (1 + i) ^ n) * (1 + i) ^ n = 1
  field_simp [hn]
