-- Prove2me | solution 1 for ActuarialValuation.pen9Salary_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:30:20.285755+00:00
-- url     : https://prove2.me/submissions/64832531-d00f-4315-a28e-f941560df021

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9Salary
open ActuarialValuation

theorem solution(s growth : ℝ) : pen9Salary s growth 0 = s := by
  simp [pen9Salary]
