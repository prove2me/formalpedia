-- Prove2me | solution 1 for ActuarialValuation.msSemiStep_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:17:36.83898+00:00
-- url     : https://prove2.me/submissions/66c2164b-2d5f-4385-838c-614b837d71c2

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msSemiStep
open ActuarialValuation

theorem solution(T : ℕ → Fin 3 → Fin 3 → ℝ) (i j : Fin 3) : msSemiStep T 0 i j = T 0 i j := by
  first
  | (simp [msSemiStep]; done)
  | (norm_num [msSemiStep]; done)
  | (unfold msSemiStep; positivity)
  | (simp only [msSemiStep]; positivity)
  | (unfold msSemiStep; ring)
  | (unfold msSemiStep; simp; done)
  | (unfold msSemiStep; norm_num; done)
  | (simp [msSemiStep]; ring)
  | (unfold msSemiStep; split_ifs <;> simp_all <;> linarith)
  | (unfold msSemiStep; nlinarith [sq_nonneg 0])
  | (simp_all [msSemiStep]; done)
  | (unfold msSemiStep; simp_all; done)
  | rfl
