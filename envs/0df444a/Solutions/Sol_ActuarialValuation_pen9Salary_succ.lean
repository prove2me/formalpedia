-- Prove2me | solution 1 for ActuarialValuation.pen9Salary_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:55:50.3042+00:00
-- url     : https://prove2.me/submissions/b3eb76bd-23d8-49ad-8def-c18ab628af75

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9Salary

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (s growth : ℝ) (n : ℕ) : pen9Salary s growth (n+1) = pen9Salary s growth n * (1+growth) := by
  simp only [pen9Salary, pow_succ]
  ring
