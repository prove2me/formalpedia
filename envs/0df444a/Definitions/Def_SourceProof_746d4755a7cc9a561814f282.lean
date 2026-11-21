-- Prove2me | Definitions.Def_SourceProof_746d4755a7cc9a561814f282
-- name    : SourceProof_746d4755a7cc9a561814f282
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:51:21.797419+00:00
-- url     : https://prove2.me/theorems/a894d9f2-fd8a-45d0-a525-1c319ea5e46e
-- title:
--   LevyStochCalc source module: SourceProof_746d4755a7cc9a561814f282
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.varClock_mono` comes from the `LevyStochCalc.Brownian.ItoFourthMomentIncrements` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentIncrements_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Moments of a Brownian increment and the partial sums of the elementary integral

The moments of a centred real Gaussian and of a Brownian increment: they scale with the standard
deviation, the odd ones vanish, and a random variable measurable before the increment factors out
of the integral against any power of it. On top of this the elementary integral of a simple
integrand is presented as the partial sums `SimplePredictable.partialSum` of its summands, with
their measurability, adaptedness and `Lᵖ` membership, and the variance budget
`SimplePredictable.varClock c k = ∑_{j < k} c_j² (τ_{j+1} − τ_j)` of a per-tile coefficient
bound `c`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section Increments

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)

end Increments

namespace SimplePredictable

variable {T : ℝ} (G : SimplePredictable Ω T)
  {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)

theorem _root_.Prove2MeSourceProof.h_746d4755a7cc9a561814f282 (c : Fin G.N → ℝ) {k l : ℕ} (h : k ≤ l) :
    G.varClock c k ≤ G.varClock c l := by
  unfold LevyStochCalc.Brownian.Ito.SimplePredictable.varClock
  have hsub : Finset.range k ⊆ Finset.range l := by
    intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => ?_
  by_cases hj : j < G.N
  · rw [dif_pos hj]
    exact mul_nonneg (sq_nonneg _)
      (sub_nonneg.mpr (G.partition_strictMono Fin.castSucc_lt_succ).le)
  · rw [dif_neg hj]
end SimplePredictable

end LevyStochCalc.Brownian.Ito


