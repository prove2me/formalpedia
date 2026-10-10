-- Prove2me | solution 1 for ActuarialValuation.cm1CareerSalarySum_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:25:59.128515+00:00
-- url     : https://prove2.me/submissions/a7e83bad-2412-4a18-b560-489d7d06fd8c

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1CareerSalarySum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (salary : ℕ → ℝ) : cm1CareerSalarySum salary 0 = 0 := by
  simp [cm1CareerSalarySum]
