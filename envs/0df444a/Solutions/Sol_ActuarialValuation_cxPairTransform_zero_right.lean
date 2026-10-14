-- Prove2me | solution 1 for ActuarialValuation.cxPairTransform_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:18:26.486475+00:00
-- url     : https://prove2.me/submissions/9acc564b-213c-42cd-8cc8-f30f7ddeff01

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxPairTransform
open ActuarialValuation

theorem solution(f g : ℕ → ℝ) (n : ℕ) (z : ℝ) : cxPairTransform f g n 0 z = 0 := by
  first
  | (simp [cxPairTransform]; done)
  | (norm_num [cxPairTransform]; done)
  | (unfold cxPairTransform; positivity)
  | (simp only [cxPairTransform]; positivity)
  | (unfold cxPairTransform; ring)
  | (unfold cxPairTransform; simp; done)
  | (unfold cxPairTransform; norm_num; done)
  | (simp [cxPairTransform]; ring)
  | (unfold cxPairTransform; split_ifs <;> simp_all <;> linarith)
  | (unfold cxPairTransform; nlinarith [sq_nonneg 0])
  | (simp_all [cxPairTransform]; done)
  | (unfold cxPairTransform; simp_all; done)
  | rfl
