-- Prove2me | solution 1 for ActuarialValuation.coFGM_zero_parameter
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:48:55.696975+00:00
-- url     : https://prove2.me/submissions/ab2f7fb1-7232-4261-bdee-bcb6cbd05353

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coInd
import Definitions.Def_actuarial_coFGM
open ActuarialValuation

theorem solution(u v : ℝ) : coFGM 0 u v=coInd u v := by
  first
  | (simp [coInd, coFGM]; done)
  | (norm_num [coInd, coFGM]; done)
  | (unfold coInd coFGM; positivity)
  | (simp only [coInd, coFGM]; positivity)
  | (unfold coInd coFGM; ring)
  | (unfold coInd coFGM; simp; done)
  | (unfold coInd coFGM; norm_num; done)
  | (simp [coInd, coFGM]; ring)
  | (unfold coInd coFGM; split_ifs <;> simp_all <;> linarith)
  | (unfold coInd coFGM; nlinarith [sq_nonneg 0])
  | (simp_all [coInd, coFGM]; done)
  | (unfold coInd coFGM; simp_all; done)
  | rfl
