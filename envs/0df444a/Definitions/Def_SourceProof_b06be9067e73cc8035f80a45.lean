-- Prove2me | Definitions.Def_SourceProof_b06be9067e73cc8035f80a45
-- name    : SourceProof_b06be9067e73cc8035f80a45
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:56:08.584813+00:00
-- url     : https://prove2.me/theorems/cdadb8cd-e691-42eb-a2f6-164c753b68d6
-- title:
--   LevyStochCalc source module: SourceProof_b06be9067e73cc8035f80a45
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.integral_partialSum_pow_four_succ` comes from the `LevyStochCalc.Brownian.ItoFourthMomentPartialSums` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Batteries.Tactic.OpenPrivate
import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F000

open private integral_add_mul_increment_pow_four from Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F000
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

theorem _root_.Prove2MeSourceProof.h_b06be9067e73cc8035f80a45 {k : ℕ} (hk : k < G.N) :
    ∫ ω, (G.partialSum W (k + 1) ω) ^ 4 ∂P
      = (∫ ω, (G.partialSum W k ω) ^ 4 ∂P)
        + 6 * ((∫ ω, (G.partialSum W k ω) ^ 2 * (G.ξ ⟨k, hk⟩ ω) ^ 2 ∂P)
          * (G.partition (⟨k, hk⟩ : Fin G.N).succ
            - G.partition (⟨k, hk⟩ : Fin G.N).castSucc))
        + (∫ ω, (G.ξ ⟨k, hk⟩ ω) ^ 4 ∂P)
          * ((G.partition (⟨k, hk⟩ : Fin G.N).succ
            - G.partition (⟨k, hk⟩ : Fin G.N).castSucc) ^ 2 * gaussianFourthMoment) := by
  have hrw : ∀ ω, G.partialSum W (k + 1) ω
      = G.partialSum W k ω + G.ξ ⟨k, hk⟩ ω
        * (W.W (G.partition (⟨k, hk⟩ : Fin G.N).succ) ω
          - W.W (G.partition (⟨k, hk⟩ : Fin G.N).castSucc) ω) := fun ω => by
    rw [G.partialSum_succ W k ω, LevyStochCalc.Brownian.Ito.SimplePredictable.term, dif_pos hk]
  simp_rw [hrw]
  exact integral_add_mul_increment_pow_four W ℱ hℱ (G.partition_nonneg _)
    (G.partition_strictMono Fin.castSucc_lt_succ)
    (G.memLp_partialSum W hC 4 (by simp) k) (G.measurable_partialSum W k)
    ((_root_.Prove2MeSourceProof.h_abcff24ab5778ee51e37f41d G) W ℱ hℱ h_adapt hk.le)
    (G.ξ_measurable _) (h_adapt ⟨k, hk⟩) hC0 (hC ⟨k, hk⟩)
end Moments

end SimplePredictable

end LevyStochCalc.Brownian.Ito


