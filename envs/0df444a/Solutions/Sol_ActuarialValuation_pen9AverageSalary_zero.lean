-- Prove2me | solution 1 for ActuarialValuation.pen9AverageSalary_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:39:12.062403+00:00
-- url     : https://prove2.me/submissions/a74cefbd-39e2-4e9c-abac-de5855588feb

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9AverageSalary
open ActuarialValuation

theorem solution(salary : ℕ → ℝ) (first : ℕ) : pen9AverageSalary salary first 0 = 0 := by
  first
  | (simp [pen9AverageSalary]; done)
  | (norm_num [pen9AverageSalary]; done)
  | (unfold pen9AverageSalary; positivity)
  | (simp only [pen9AverageSalary]; positivity)
  | (unfold pen9AverageSalary; ring)
  | (unfold pen9AverageSalary; simp; done)
  | (unfold pen9AverageSalary; norm_num; done)
  | (simp [pen9AverageSalary]; ring)
  | (unfold pen9AverageSalary; split_ifs <;> simp_all <;> linarith)
  | (unfold pen9AverageSalary; nlinarith [sq_nonneg 0])
  | (simp_all [pen9AverageSalary]; done)
  | (unfold pen9AverageSalary; simp_all; done)
  | rfl
