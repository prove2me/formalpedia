-- Prove2me | solution 1 for ActuarialValuation.siFixedMean_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:39:59.199927+00:00
-- url     : https://prove2.me/submissions/74aa0889-1861-41a9-a7b4-dc1a6f01e363

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siFixedMean
import Definitions.Def_actuarial_siGrossMean
open ActuarialValuation

theorem solution{m : ℕ} (p : Fin m → ℝ) (r : Fin m → ℝ) : siFixedMean p r 1=siGrossMean p r := by
  first
  | (simp [siFixedMean, siFixedAccum, siGrowth, siMean, siGrossMean]; done)
  | (norm_num [siFixedMean, siFixedAccum, siGrowth, siMean, siGrossMean]; done)
  | (unfold siFixedMean siFixedAccum siGrowth siMean siGrossMean; positivity)
  | (simp only [siFixedMean, siFixedAccum, siGrowth, siMean, siGrossMean]; positivity)
  | (unfold siFixedMean siFixedAccum siGrowth siMean siGrossMean; ring)
  | (unfold siFixedMean siFixedAccum siGrowth siMean siGrossMean; simp; done)
  | (unfold siFixedMean siFixedAccum siGrowth siMean siGrossMean; norm_num; done)
  | (simp [siFixedMean, siFixedAccum, siGrowth, siMean, siGrossMean]; ring)
  | (unfold siFixedMean siFixedAccum siGrowth siMean siGrossMean; split_ifs <;> simp_all <;> linarith)
  | (unfold siFixedMean siFixedAccum siGrowth siMean siGrossMean; nlinarith [sq_nonneg 0])
  | (simp_all [siFixedMean, siFixedAccum, siGrowth, siMean, siGrossMean]; done)
  | (unfold siFixedMean siFixedAccum siGrowth siMean siGrossMean; simp_all; done)
  | rfl
