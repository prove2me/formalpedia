-- Prove2me | solution 1 for ActuarialAnnuities.level_arithmetic_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T07:15:53.579255+00:00
-- url     : https://prove2.me/submissions/7234b211-3b91-416d-a4e6-cbe6d389dc22

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bLevel
import Definitions.Def_actuarial_bArithmetic
open ActuarialAnnuities

theorem solution(a j : ℕ) (c : ℝ) : bArithmetic a c 0 j = bLevel c j := by
  first
  | (simp [bLevel, bArithmetic]; done)
  | (norm_num [bLevel, bArithmetic]; done)
  | (unfold bLevel bArithmetic; positivity)
  | (simp only [bLevel, bArithmetic]; positivity)
  | (unfold bLevel bArithmetic; ring)
  | (unfold bLevel bArithmetic; simp; done)
  | (unfold bLevel bArithmetic; norm_num; done)
  | (simp [bLevel, bArithmetic]; ring)
  | (unfold bLevel bArithmetic; split_ifs <;> simp_all <;> linarith)
  | (unfold bLevel bArithmetic; nlinarith [sq_nonneg 0])
  | (simp_all [bLevel, bArithmetic]; done)
  | (unfold bLevel bArithmetic; simp_all; done)
  | rfl
