-- Prove2me | solution 1 for ActuarialValuation.cm1IncreasingImmediate_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:15:43.009059+00:00
-- url     : https://prove2.me/submissions/a9dbec8d-980a-434c-88a7-c05f8831618c

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1IncreasingImmediate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (i : ℝ) : cm1IncreasingImmediate i 0 = 0 := by
  simp [cm1IncreasingImmediate]
