-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F002
-- name    : LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:59:42.532284+00:00
-- url     : https://prove2.me/theorems/6e78e163-aa16-4fc7-a07c-38ef7581aa40
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoFourthMomentPartialSums
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoFourthMomentPartialSums. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Batteries.Tactic.OpenPrivate
import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F001
import Definitions.Def_SourceProof_b318e5fb0469045362086285

open private LevyStochCalc.Brownian.Ito.SimplePredictable.integral_xi_even_le integral_xi_even_le from Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F001
namespace LevyStochCalc.Brownian.Ito.SimplePredictable
export private integral_xi_even_le from Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F001
end LevyStochCalc.Brownian.Ito.SimplePredictable
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
/-- **Fourth-moment bound for the elementary integral of a uniformly bounded simple
integrand.** -/
theorem integral_simpleIntegral_pow_four_le :
    ∫ ω, (simpleIntegral W G T ω) ^ 4 ∂P
      ≤ (6 + gaussianFourthMoment) * C ^ 4 * G.partition (Fin.last G.N) ^ 2 := by
  have hcard := (_root_.Prove2MeSourceProof.h_b318e5fb0469045362086285 G) W ℱ hℱ h_adapt hC0 hC G.N le_rfl
  have hfun : ∀ ω, G.partialSum W G.N ω = simpleIntegral W G T ω := G.partialSum_card W
  simp_rw [hfun] at hcard
  have hlast : G.partition (⟨G.N, Nat.lt_succ_of_le le_rfl⟩ : Fin (G.N + 1))
      = G.partition (Fin.last G.N) := rfl
  rw [hlast] at hcard
  calc ∫ ω, (simpleIntegral W G T ω) ^ 4 ∂P
      ≤ 6 * C ^ 4 * (G.partition (Fin.last G.N) * G.partition (Fin.last G.N))
        + gaussianFourthMoment * C ^ 4 * G.partition (Fin.last G.N) ^ 2 := hcard
    _ = (6 + gaussianFourthMoment) * C ^ 4 * G.partition (Fin.last G.N) ^ 2 := by ring
include hℱ h_adapt hC0 hC in
/-- The fourth-moment bound stated on the horizon. -/
theorem integral_simpleIntegral_pow_four_le_horizon :
    ∫ ω, (simpleIntegral W G T ω) ^ 4 ∂P
      ≤ (6 + gaussianFourthMoment) * C ^ 4 * T ^ 2 := by
  refine (G.integral_simpleIntegral_pow_four_le W ℱ hℱ h_adapt hC0 hC).trans ?_
  have h1 : G.partition (Fin.last G.N) ≤ T := G.partition_le_T
  have h2 : (0 : ℝ) ≤ G.partition (Fin.last G.N) := G.partition_nonneg _
  have h3 : (0 : ℝ) ≤ 6 + gaussianFourthMoment := by
    linarith [gaussianFourthMoment_nonneg]
  have h4 : G.partition (Fin.last G.N) ^ 2 ≤ T ^ 2 := by nlinarith
  nlinarith [pow_nonneg hC0 4, mul_nonneg h3 (pow_nonneg hC0 4)]
include hℱ h_adapt hC0 hC in
/-- Second moment of a partial sum against a per-tile coefficient bound. -/
theorem integral_partialSum_sq_le_varClock {c : Fin G.N → ℝ}
    (hc : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ c i) :
    ∀ (k : ℕ) (_hk : k ≤ G.N),
      ∫ ω, (G.partialSum W k ω) ^ 2 ∂P ≤ G.varClock c k := by
  intro k
  induction k with
  | zero =>
    intro _
    have h0 : ∀ ω, G.partialSum W 0 ω = 0 := G.partialSum_zero W
    simp_rw [h0]
    simp [G.varClock_zero]
  | succ n ih =>
    intro hk
    have hn : n < G.N := hk
    have hΔ0 : (0 : ℝ) ≤ G.partition (⟨n, hn⟩ : Fin G.N).succ
        - G.partition (⟨n, hn⟩ : Fin G.N).castSucc :=
      sub_nonneg.mpr (G.partition_strictMono Fin.castSucc_lt_succ).le
    rw [G.integral_partialSum_sq_succ W ℱ hℱ h_adapt hC0 hC hn, G.varClock_succ c hn]
    have h1 := ih hn.le
    have h2 : ∫ ω, (G.ξ ⟨n, hn⟩ ω) ^ 2 ∂P ≤ c ⟨n, hn⟩ ^ 2 := by
      simpa using G.integral_xi_even_le (P := P) ⟨n, hn⟩ (hc ⟨n, hn⟩) 1
    linarith [mul_le_mul_of_nonneg_right h2 hΔ0]
end Moments

end SimplePredictable

end LevyStochCalc.Brownian.Ito


