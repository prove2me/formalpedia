-- Prove2me | solution 1 for ActuarialValuation.pensionLatePostponedValue_zero_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:11:58.578981+00:00
-- url     : https://prove2.me/submissions/92f78617-1ee4-4c3b-8e7b-65081cdad29f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pensionLatePostponedValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (D p v m A : ℝ) :
  pensionLatePostponedValue D p v m A 0 = D := by
  simp [pensionLatePostponedValue]
