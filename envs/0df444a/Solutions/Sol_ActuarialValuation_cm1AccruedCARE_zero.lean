-- Prove2me | solution 1 for ActuarialValuation.cm1AccruedCARE_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:34:31.595989+00:00
-- url     : https://prove2.me/submissions/b4ca7c86-4882-45f6-8bcc-816eb8fcfda8

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1AccruedCARE

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (salary revalue : ℕ → ℝ) (a : ℝ) : cm1AccruedCARE salary revalue 0 a = 0 := by
  simp [cm1AccruedCARE]
