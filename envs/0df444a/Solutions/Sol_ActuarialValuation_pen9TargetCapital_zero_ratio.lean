-- Prove2me | solution 1 for ActuarialValuation.pen9TargetCapital_zero_ratio
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:14:00.989669+00:00
-- url     : https://prove2.me/submissions/7cdadddc-7e54-45f8-986e-aeadcff4c31f

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9TargetCapital
open ActuarialValuation

theorem solution(salary ann : ℝ) : pen9TargetCapital salary 0 ann = 0 := by
  first
  | (simp [pen9TargetCapital]; done)
  | (norm_num [pen9TargetCapital]; done)
  | (unfold pen9TargetCapital; positivity)
  | (simp only [pen9TargetCapital]; positivity)
  | (unfold pen9TargetCapital; ring)
  | (unfold pen9TargetCapital; simp; done)
  | (unfold pen9TargetCapital; norm_num; done)
  | (simp [pen9TargetCapital]; ring)
  | (unfold pen9TargetCapital; split_ifs <;> simp_all <;> linarith)
  | (unfold pen9TargetCapital; nlinarith [sq_nonneg 0])
  | (simp_all [pen9TargetCapital]; done)
  | (unfold pen9TargetCapital; simp_all; done)
  | rfl
