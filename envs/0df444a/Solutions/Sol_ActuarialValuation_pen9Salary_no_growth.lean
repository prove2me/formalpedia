-- Prove2me | solution 1 for ActuarialValuation.pen9Salary_no_growth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:57:00.773392+00:00
-- url     : https://prove2.me/submissions/303ae064-af8c-4e77-a87b-c67b132f30d3

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9Salary

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (s : ℝ) (n : ℕ) : pen9Salary s 0 n = s := by
  simp [pen9Salary]
