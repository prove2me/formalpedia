-- Prove2me | solution 1 for ActuarialValuation.finiteReserveInnovationValue_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:24:43.915475+00:00
-- url     : https://prove2.me/submissions/ca21d5f4-30f1-42e4-9d09-4ced294d6a14

import Mathlib
import Definitions.Def_actuarial_finiteReserveInnovationValue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (K : ℕ) (v : ℝ) (benefit reserve q : ℕ → ℝ) :
    finiteReserveInnovationValue K 0 v benefit reserve q = 0 := by
  simp [finiteReserveInnovationValue]
