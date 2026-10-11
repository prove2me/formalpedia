-- Prove2me | solution 1 for ActuarialValuation.clUltimate_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T19:53:26.099973+00:00
-- url     : https://prove2.me/submissions/07761e28-32b7-4410-8add-ce888a46b9da

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clUltimate
open ActuarialValuation

theorem solution(f : ℝ) : clUltimate 0 f = 0 := by
  first
  | (simp [clUltimate]; done)
  | (norm_num [clUltimate]; done)
  | (unfold clUltimate; positivity)
  | (simp only [clUltimate]; positivity)
  | (unfold clUltimate; ring)
  | (unfold clUltimate; simp; done)
  | (unfold clUltimate; norm_num; done)
  | (simp [clUltimate]; ring)
  | (unfold clUltimate; split_ifs <;> simp_all <;> linarith)
  | (unfold clUltimate; nlinarith [sq_nonneg 0])
  | rfl
