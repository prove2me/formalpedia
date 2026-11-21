-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F003
-- name    : LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:03:41.609177+00:00
-- url     : https://prove2.me/theorems/b0206144-fa7c-48e2-b11c-1c59ebca89d0
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoFourthMomentPartialSums
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoFourthMomentPartialSums. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentIncrements_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentIncrements_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentIncrements_F002
import Definitions.Def_SourceProof_4bba863570ba53ef5f94bc24

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Second and fourth moments of the elementary Brownian integral

The moment recursion over the partial sums of the elementary integral of a simple integrand: one
step adds the second moment of the new tile, and in the fourth-moment recursion the odd-power
cross terms drop out because a coefficient measurable before an increment is independent of it.
Iterating gives `𝔼|∫_0^T H dW|⁴ ≤ (6 + c)·C⁴·T²` for an integrand bounded by `C`, where `c` is
the fourth moment of the standard Gaussian, and the sharper form
`𝔼|∫_0^T H dW|⁴ ≤ (6 + c)·(∑_j c_j² Δ_j)²` against a per-tile coefficient bound `c`, which for a
coefficient vanishing off a subinterval sees only that subinterval's length.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

namespace SimplePredictable

variable {T : ℝ} (G : SimplePredictable Ω T)
  {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)

section Moments

variable (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)

include hℱ h_adapt hC0 hC in
/-- **Fourth-moment bound for the elementary integral against a per-tile coefficient
bound.** -/
theorem integral_simpleIntegral_pow_four_le_varClock {c : Fin G.N → ℝ}
    (hc : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ c i) :
    ∫ ω, (simpleIntegral W G T ω) ^ 4 ∂P
      ≤ (6 + gaussianFourthMoment) * G.varClock c G.N ^ 2 := by
  have hcard := (_root_.Prove2MeSourceProof.h_4bba863570ba53ef5f94bc24 G) W ℱ hℱ h_adapt hC0 hC hc G.N le_rfl
  have hfun : ∀ ω, G.partialSum W G.N ω = simpleIntegral W G T ω := G.partialSum_card W
  simp_rw [hfun] at hcard
  calc ∫ ω, (simpleIntegral W G T ω) ^ 4 ∂P
      ≤ 6 * (G.varClock c G.N * G.varClock c G.N)
        + gaussianFourthMoment * G.varClock c G.N ^ 2 := hcard
    _ = (6 + gaussianFourthMoment) * G.varClock c G.N ^ 2 := by ring
end Moments

end SimplePredictable

end LevyStochCalc.Brownian.Ito


