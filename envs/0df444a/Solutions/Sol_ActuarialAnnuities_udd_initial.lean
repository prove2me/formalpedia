-- Prove2me | solution 1 for ActuarialAnnuities.udd_initial
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T07:13:33.997767+00:00
-- url     : https://prove2.me/submissions/490520c7-90db-4f38-b883-6113f53cf0fd

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bUDD
open ActuarialAnnuities

theorem solution(s0 s1 : ℝ) : bUDD s0 s1 0 = s0 := by
  first
  | (simp [bUDD]; done)
  | (norm_num [bUDD]; done)
  | (unfold bUDD; positivity)
  | (simp only [bUDD]; positivity)
  | (unfold bUDD; ring)
  | (unfold bUDD; simp; done)
  | (unfold bUDD; norm_num; done)
  | (simp [bUDD]; ring)
  | (unfold bUDD; split_ifs <;> simp_all <;> linarith)
  | (unfold bUDD; nlinarith [sq_nonneg 0])
  | (simp_all [bUDD]; done)
  | (unfold bUDD; simp_all; done)
  | rfl
