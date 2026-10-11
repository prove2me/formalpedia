-- Prove2me | solution 1 for ActuarialValuation.kmExitCount_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:05:44.409699+00:00
-- url     : https://prove2.me/submissions/efa76288-7043-42df-8987-14a080bb549e

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmExitCount
open ActuarialValuation

theorem solution(d : ℝ) : kmExitCount d 0 = d := by
  first
  | (simp [kmExitCount]; done)
  | (norm_num [kmExitCount]; done)
  | (unfold kmExitCount; positivity)
  | (simp only [kmExitCount]; positivity)
  | (unfold kmExitCount; ring)
  | (unfold kmExitCount; simp; done)
  | (unfold kmExitCount; norm_num; done)
  | (simp [kmExitCount]; ring)
  | (unfold kmExitCount; split_ifs <;> simp_all <;> linarith)
  | (unfold kmExitCount; nlinarith [sq_nonneg 0])
  | (simp_all [kmExitCount]; done)
  | (unfold kmExitCount; simp_all; done)
  | rfl
