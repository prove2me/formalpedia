-- Prove2me | solution 1 for ActuarialValuation.cm1FinalSalaryPension_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:30:32.822423+00:00
-- url     : https://prove2.me/submissions/0b0aa9b6-70af-4cd0-a0fe-c1d3f5015962

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1FinalSalaryPension

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (salary : ℕ → ℝ) (accrual : ℝ) : cm1FinalSalaryPension salary 0 accrual = 0 := by
  simp [cm1FinalSalaryPension]
