-- Prove2me | solution 1 for ActuarialValuation.cm1AnnuityImmediate_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:14:50.637728+00:00
-- url     : https://prove2.me/submissions/0ecb5d2f-061d-44d8-867c-dbb13439c8db

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1AnnuityImmediate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (i : ℝ) : cm1AnnuityImmediate i 0 = 0 := by
  simp [cm1AnnuityImmediate]
