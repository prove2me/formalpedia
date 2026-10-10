-- Prove2me | solution 1 for ActuarialValuation.cm1Accum_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:11:35.458969+00:00
-- url     : https://prove2.me/submissions/92909c80-bcf9-409a-9472-bc0420cefdc1

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1Accum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (i : ℝ) (m n : ℕ) : cm1Accum i (m+n) = cm1Accum i m * cm1Accum i n := by
  simp [cm1Accum, pow_add]
