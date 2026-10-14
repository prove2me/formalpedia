-- Prove2me | solution 1 for ActuarialValuation.msTwoStep_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T14:06:37.110217+00:00
-- url     : https://prove2.me/submissions/33fe1c2c-5e29-451f-bdbf-237e0fc59c69

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msTwoStep
open ActuarialValuation

theorem solution(T : Fin 3 → Fin 3 → ℝ) (i k : Fin 3) : msTwoStep T (fun _ _ => 0) i k = 0 := by
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
