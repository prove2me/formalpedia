-- Prove2me | solution 1 for ActuarialValuation.siFixedAccum_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:01:55.808541+00:00
-- url     : https://prove2.me/submissions/dfb37c35-ba7d-42bc-bb5e-d2879265f7e2

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siFixedAccum
open ActuarialValuation

theorem solution(i : ℝ) : siFixedAccum i 0=1 := by
  first
  | (simp [siFixedAccum, siGrowth]; done)
  | (norm_num [siFixedAccum, siGrowth]; done)
  | (unfold siFixedAccum siGrowth; positivity)
  | (simp only [siFixedAccum, siGrowth]; positivity)
  | (unfold siFixedAccum siGrowth; ring)
  | (unfold siFixedAccum siGrowth; simp; done)
  | (unfold siFixedAccum siGrowth; norm_num; done)
  | (simp [siFixedAccum, siGrowth]; ring)
  | (unfold siFixedAccum siGrowth; split_ifs <;> simp_all <;> linarith)
  | (unfold siFixedAccum siGrowth; nlinarith [sq_nonneg 0])
  | rfl
