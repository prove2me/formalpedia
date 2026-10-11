-- Prove2me | solution 1 for ActuarialValuation.pen9MidSalary_symm
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:48:40.102759+00:00
-- url     : https://prove2.me/submissions/9c1c29ca-fbdf-4eb0-bed0-d5f81987e662

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9MidSalary
open ActuarialValuation

theorem solution(a b : ℝ) : pen9MidSalary a b = pen9MidSalary b a := by
  unfold pen9MidSalary
  ring
