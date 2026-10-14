-- Prove2me | solution 1 for ActuarialValuation.msTwoStep_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:58:01.924074+00:00
-- url     : https://prove2.me/submissions/6bf0b997-c9ba-465d-9275-049811419d0c

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msTwoStep
open ActuarialValuation

theorem solution(U : Fin 3 → Fin 3 → ℝ) (i k : Fin 3) : msTwoStep (fun _ _ => 0) U i k = 0 := by
  first
  | (simp [msTwoStep]; done)
  | (norm_num [msTwoStep]; done)
  | (unfold msTwoStep; positivity)
  | (simp only [msTwoStep]; positivity)
  | (unfold msTwoStep; ring)
  | (unfold msTwoStep; simp; done)
  | (unfold msTwoStep; norm_num; done)
  | (simp [msTwoStep]; ring)
  | (unfold msTwoStep; split_ifs <;> simp_all <;> linarith)
  | (unfold msTwoStep; nlinarith [sq_nonneg 0])
  | (simp_all [msTwoStep]; done)
  | (unfold msTwoStep; simp_all; done)
  | rfl
