-- Prove2me | solution 1 for ActuarialValuation.cm1Accum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:24:54.661801+00:00
-- url     : https://prove2.me/submissions/1bb0cb6d-690f-4562-b6e8-380513c1b050

import Mathlib.Tactic
import Definitions.Def_actuarial_cm1Accum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (i : ℝ) (n : ℕ) (hi : -1 < i) : 0 < cm1Accum i n := by
  have hp : 0 < 1 + i := by linarith
  simpa only [cm1Accum] using (pow_pos hp n)
