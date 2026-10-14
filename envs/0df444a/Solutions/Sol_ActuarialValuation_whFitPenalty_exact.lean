-- Prove2me | solution 1 for ActuarialValuation.whFitPenalty_exact
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T16:10:14.924989+00:00
-- url     : https://prove2.me/submissions/31c3ce58-8d6d-4a93-b232-061a0021d513

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whFitPenalty
open ActuarialValuation

theorem solution(w g : ℕ → ℝ) (n : ℕ) : whFitPenalty w g g n = 0 := by
  first
  | (simp [whFitPenalty, whWeightedFit, whSquaredResidual, whRateResidual]; done)
  | (norm_num [whFitPenalty, whWeightedFit, whSquaredResidual, whRateResidual]; done)
  | (unfold whFitPenalty whWeightedFit whSquaredResidual whRateResidual; positivity)
  | (simp only [whFitPenalty, whWeightedFit, whSquaredResidual, whRateResidual]; positivity)
  | (unfold whFitPenalty whWeightedFit whSquaredResidual whRateResidual; ring)
  | (unfold whFitPenalty whWeightedFit whSquaredResidual whRateResidual; simp; done)
  | (unfold whFitPenalty whWeightedFit whSquaredResidual whRateResidual; norm_num; done)
  | (simp [whFitPenalty, whWeightedFit, whSquaredResidual, whRateResidual]; ring)
  | (unfold whFitPenalty whWeightedFit whSquaredResidual whRateResidual; split_ifs <;> simp_all <;> linarith)
  | (unfold whFitPenalty whWeightedFit whSquaredResidual whRateResidual; nlinarith [sq_nonneg 0])
  | (simp_all [whFitPenalty, whWeightedFit, whSquaredResidual, whRateResidual]; done)
  | (unfold whFitPenalty whWeightedFit whSquaredResidual whRateResidual; simp_all; done)
  | rfl
