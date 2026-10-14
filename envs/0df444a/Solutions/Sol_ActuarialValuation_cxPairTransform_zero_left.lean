-- Prove2me | solution 1 for ActuarialValuation.cxPairTransform_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:00:39.568923+00:00
-- url     : https://prove2.me/submissions/7df3f5b7-0d3a-43e2-b790-4d45db7596ba

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxPairTransform
open ActuarialValuation

theorem solution(f g : ℕ → ℝ) (m : ℕ) (z : ℝ) : cxPairTransform f g 0 m z = 0 := by
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
