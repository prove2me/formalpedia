-- Prove2me | solution 1 for ActuarialValuation.cm1SecondMomentNumerator_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:17:28.417988+00:00
-- url     : https://prove2.me/submissions/bcb6f6c4-3c24-42ab-9a31-012a8f8d58bf

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1SecondMomentNumerator
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c : ℕ → ℝ) (i : ℝ) : cm1SecondMomentNumerator c 0 i = 0 := by
  simp [cm1SecondMomentNumerator]
