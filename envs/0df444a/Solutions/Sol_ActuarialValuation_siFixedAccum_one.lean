-- Prove2me | solution 1 for ActuarialValuation.siFixedAccum_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:48:52.741955+00:00
-- url     : https://prove2.me/submissions/28bb14c1-8e1f-4c3e-9606-1d125f43ae6c

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siGrowth
import Definitions.Def_actuarial_siFixedAccum
open ActuarialValuation

theorem solution(i : ℝ) : siFixedAccum i 1=siGrowth i := by
  first
  | (simp [siGrowth, siFixedAccum]; done)
  | (norm_num [siGrowth, siFixedAccum]; done)
  | (unfold siGrowth siFixedAccum; positivity)
  | (simp only [siGrowth, siFixedAccum]; positivity)
  | (unfold siGrowth siFixedAccum; ring)
  | (unfold siGrowth siFixedAccum; simp; done)
  | (unfold siGrowth siFixedAccum; norm_num; done)
  | (simp [siGrowth, siFixedAccum]; ring)
  | (unfold siGrowth siFixedAccum; split_ifs <;> simp_all <;> linarith)
  | (unfold siGrowth siFixedAccum; nlinarith [sq_nonneg 0])
  | (simp_all [siGrowth, siFixedAccum]; done)
  | (unfold siGrowth siFixedAccum; simp_all; done)
  | rfl
