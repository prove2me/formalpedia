-- Prove2me | solution 1 for ActuarialValuation.negBinCountVariance_ge_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:16:11.796562+00:00
-- url     : https://prove2.me/submissions/691dfe88-8a0f-4500-9e97-78222202a94e

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinCountMean
import Definitions.Def_actuarial_negBinCountVariance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r : ℕ) (p : ℝ)
  (hp0 : 0 ≤ p) (hp1 : p < 1) :
  negBinCountMean r p ≤ negBinCountVariance r p := by
  unfold negBinCountMean negBinCountVariance
  have hden : 0 < 1 - p := by
    linarith
  have hden2 : 0 < (1 - p) ^ 2 := sq_pos_of_pos hden
  apply (div_le_div_iff₀ hden hden2).2
  have hr : 0 ≤ (r : ℝ) := by positivity
  have hprod : 0 ≤ (r : ℝ) * p := mul_nonneg hr hp0
  have hdp : 0 ≤ (1 - p) * p := mul_nonneg hden.le hp0
  have hstep : (1 - p) ^ 2 ≤ 1 - p := by
    nlinarith [hdp]
  have hscaled := mul_le_mul_of_nonneg_left hstep hprod
  simpa [mul_assoc] using hscaled
