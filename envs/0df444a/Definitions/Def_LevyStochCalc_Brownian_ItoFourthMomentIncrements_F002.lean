-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentIncrements_F002
-- name    : LevyStochCalc_Brownian_ItoFourthMomentIncrements_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:49:21.139391+00:00
-- url     : https://prove2.me/theorems/ee5edfca-3ae2-4300-977b-dc79a46fb2ab
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoFourthMomentIncrements
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoFourthMomentIncrements. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraProduct_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraProduct_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraProduct_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand_F001

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

/-- The variance budget of the first `k` tiles for a per-tile coefficient bound `c`:
`∑_{j < k} c_j² (τ_{j+1} − τ_j)`. -/
noncomputable def varClock (c : Fin G.N → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, if h : j < G.N then
    c ⟨j, h⟩ ^ 2 * (G.partition (⟨j, h⟩ : Fin G.N).succ
      - G.partition (⟨j, h⟩ : Fin G.N).castSucc) else 0
theorem varClock_zero (c : Fin G.N → ℝ) : G.varClock c 0 = 0 := by simp [varClock]
theorem varClock_succ (c : Fin G.N → ℝ) {k : ℕ} (hk : k < G.N) :
    G.varClock c (k + 1) = G.varClock c k
      + c ⟨k, hk⟩ ^ 2 * (G.partition (⟨k, hk⟩ : Fin G.N).succ
        - G.partition (⟨k, hk⟩ : Fin G.N).castSucc) := by
  unfold varClock
  rw [Finset.sum_range_succ, dif_pos hk]
theorem varClock_nonneg (c : Fin G.N → ℝ) (k : ℕ) : 0 ≤ G.varClock c k := by
  unfold varClock
  refine Finset.sum_nonneg fun j _ => ?_
  by_cases h : j < G.N
  · rw [dif_pos h]
    exact mul_nonneg (sq_nonneg _)
      (sub_nonneg.mpr (G.partition_strictMono Fin.castSucc_lt_succ).le)
  · rw [dif_neg h]
end SimplePredictable

end LevyStochCalc.Brownian.Ito


