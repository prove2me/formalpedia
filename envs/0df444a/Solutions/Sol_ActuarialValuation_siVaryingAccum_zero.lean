-- Prove2me | solution 1 for ActuarialValuation.siVaryingAccum_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:48:49.721198+00:00
-- url     : https://prove2.me/submissions/0c8a0b04-2a06-4032-b0c3-fd632bea5fc8

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siVaryingAccum
open ActuarialValuation

theorem solution(r : ℕ → ℝ) : siVaryingAccum r 0=1 := by
  first
  | (simp [siVaryingAccum, siGrowth]; done)
  | (norm_num [siVaryingAccum, siGrowth]; done)
  | (unfold siVaryingAccum siGrowth; positivity)
  | (simp only [siVaryingAccum, siGrowth]; positivity)
  | (unfold siVaryingAccum siGrowth; ring)
  | (unfold siVaryingAccum siGrowth; simp; done)
  | (unfold siVaryingAccum siGrowth; norm_num; done)
  | (simp [siVaryingAccum, siGrowth]; ring)
  | (unfold siVaryingAccum siGrowth; split_ifs <;> simp_all <;> linarith)
  | (unfold siVaryingAccum siGrowth; nlinarith [sq_nonneg 0])
  | (simp_all [siVaryingAccum, siGrowth]; done)
  | (unfold siVaryingAccum siGrowth; simp_all; done)
  | rfl
