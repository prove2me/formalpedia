-- Prove2me | solution 1 for ActuarialValuation.kmGreenwoodTerm_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:53:46.784114+00:00
-- url     : https://prove2.me/submissions/50e66ea0-ab67-4012-b945-20d3920827b0

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmGreenwoodTerm
open ActuarialValuation

theorem solution(r : ℝ) : kmGreenwoodTerm 0 r = 0 := by
  first
  | (simp [kmGreenwoodTerm]; done)
  | (norm_num [kmGreenwoodTerm]; done)
  | (unfold kmGreenwoodTerm; positivity)
  | (simp only [kmGreenwoodTerm]; positivity)
  | (unfold kmGreenwoodTerm; ring)
  | (unfold kmGreenwoodTerm; simp; done)
  | (unfold kmGreenwoodTerm; norm_num; done)
  | (simp [kmGreenwoodTerm]; ring)
  | (unfold kmGreenwoodTerm; split_ifs <;> simp_all <;> linarith)
  | (unfold kmGreenwoodTerm; nlinarith [sq_nonneg 0])
  | (simp_all [kmGreenwoodTerm]; done)
  | (unfold kmGreenwoodTerm; simp_all; done)
  | rfl
