-- Prove2me | solution 1 for ActuarialValuation.pen9DeathServicePV_zero_death
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:37:25.890211+00:00
-- url     : https://prove2.me/submissions/a4e7a7ad-4cc9-4271-b8a1-69aec31ed378

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9DeathServicePV
open ActuarialValuation

theorem solution(s cover ann v : ℝ) : pen9DeathServicePV 0 s cover ann v = 0 := by
  first
  | (simp [pen9DeathServicePV]; done)
  | (norm_num [pen9DeathServicePV]; done)
  | (unfold pen9DeathServicePV; positivity)
  | (simp only [pen9DeathServicePV]; positivity)
  | (unfold pen9DeathServicePV; ring)
  | (unfold pen9DeathServicePV; simp; done)
  | (unfold pen9DeathServicePV; norm_num; done)
  | (simp [pen9DeathServicePV]; ring)
  | (unfold pen9DeathServicePV; split_ifs <;> simp_all <;> linarith)
  | (unfold pen9DeathServicePV; nlinarith [sq_nonneg 0])
  | (simp_all [pen9DeathServicePV]; done)
  | (unfold pen9DeathServicePV; simp_all; done)
  | rfl
