-- Prove2me | solution 1 for ActuarialValuation.kmDeathHazard_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:26:06.791456+00:00
-- url     : https://prove2.me/submissions/41436527-fd11-4858-a68c-9db78a6e7457

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmDeathHazard
open ActuarialValuation

theorem solution(r : ℝ) : kmDeathHazard 0 r = 0 := by
  first
  | (simp [kmDeathHazard]; done)
  | (norm_num [kmDeathHazard]; done)
  | (unfold kmDeathHazard; positivity)
  | (simp only [kmDeathHazard]; positivity)
  | (unfold kmDeathHazard; ring)
  | (unfold kmDeathHazard; simp; done)
  | (unfold kmDeathHazard; norm_num; done)
  | (simp [kmDeathHazard]; ring)
  | (unfold kmDeathHazard; split_ifs <;> simp_all <;> linarith)
  | (unfold kmDeathHazard; nlinarith [sq_nonneg 0])
  | (simp_all [kmDeathHazard]; done)
  | (unfold kmDeathHazard; simp_all; done)
  | rfl
