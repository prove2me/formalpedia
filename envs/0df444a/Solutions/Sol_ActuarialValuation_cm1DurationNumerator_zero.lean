-- Prove2me | solution 1 for ActuarialValuation.cm1DurationNumerator_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:15:48.112758+00:00
-- url     : https://prove2.me/submissions/1a7b2da5-40e8-492d-a9b7-c3af22b28531

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1DurationNumerator
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c : ℕ → ℝ) (i : ℝ) : cm1DurationNumerator c 0 i = 0 := by
  simp [cm1DurationNumerator]
