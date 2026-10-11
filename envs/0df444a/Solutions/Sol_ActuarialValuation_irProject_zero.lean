-- Prove2me | solution 1 for ActuarialValuation.irProject_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:01:52.968784+00:00
-- url     : https://prove2.me/submissions/b57c0f43-e3ce-443e-aa7a-bd5551f6cb1e

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irProject
open ActuarialValuation

theorem solution(link : ℝ) : irProject 0 link=0 := by
  first
  | (simp [irProject]; done)
  | (norm_num [irProject]; done)
  | (unfold irProject; positivity)
  | (simp only [irProject]; positivity)
  | (unfold irProject; ring)
  | (unfold irProject; simp; done)
  | (unfold irProject; norm_num; done)
  | (simp [irProject]; ring)
  | (unfold irProject; split_ifs <;> simp_all <;> linarith)
  | (unfold irProject; nlinarith [sq_nonneg 0])
  | rfl
