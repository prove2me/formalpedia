-- Prove2me | solution 1 for ActuarialValuation.cm1CARELiability_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:33:15.306354+00:00
-- url     : https://prove2.me/submissions/b08cb901-f999-4005-8970-cf281d113d9d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1CARELiability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (salary revalue : ℕ → ℝ) (a annuity : ℝ) :
    cm1CARELiability salary revalue 0 a annuity = 0 := by
  simp [cm1CARELiability, cm1PensionCapitalValue, cm1AccruedCARE]
