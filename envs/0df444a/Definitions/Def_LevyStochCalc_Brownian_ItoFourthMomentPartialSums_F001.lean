-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F001
-- name    : LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:55:45.97755+00:00
-- url     : https://prove2.me/theorems/514370f1-cdba-443d-b433-ecd96427bfb1
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoFourthMomentPartialSums
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoFourthMomentPartialSums. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F000

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

/-- A coefficient bounded by `c` has even moments at most the matching power of `c`. -/
private theorem integral_xi_even_le {c : ℝ} (i : Fin G.N)
    (hci : ∀ ω, |G.ξ i ω| ≤ c) (m : ℕ) :
    ∫ ω, (G.ξ i ω) ^ (2 * m) ∂P ≤ c ^ (2 * m) := by
  have hnn : ∀ ω, (0 : ℝ) ≤ (G.ξ i ω) ^ (2 * m) := fun ω => by
    rw [pow_mul]; positivity
  have hcnn : (0 : ℝ) ≤ c ^ (2 * m) := by rw [pow_mul]; positivity
  have hpow : ∀ ω, (G.ξ i ω) ^ (2 * m) ≤ c ^ (2 * m) := fun ω => by
    have h : |G.ξ i ω| ^ (2 * m) ≤ c ^ (2 * m) :=
      pow_le_pow_left₀ (abs_nonneg _) (hci ω) _
    rwa [← abs_pow, abs_of_nonneg (hnn ω)] at h
  have hint : Integrable (fun ω => (G.ξ i ω) ^ (2 * m)) P := by
    refine (integrable_const (c ^ (2 * m))).mono
      ((G.ξ_measurable _).pow_const _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hnn ω), abs_of_nonneg hcnn]
    exact hpow ω
  calc ∫ ω, (G.ξ i ω) ^ (2 * m) ∂P ≤ ∫ _ω : Ω, c ^ (2 * m) ∂P :=
        integral_mono hint (integrable_const _) hpow
    _ = c ^ (2 * m) := by simp
include hC in
/-- A bounded coefficient has second moment at most `C²`. -/
private theorem integral_xi_sq_le (i : Fin G.N) : ∫ ω, (G.ξ i ω) ^ 2 ∂P ≤ C ^ 2 := by
  simpa using G.integral_xi_even_le (P := P) i (hC i) 1
include hC in
/-- A bounded coefficient has fourth moment at most `C⁴`. -/
private theorem integral_xi_pow_four_le (i : Fin G.N) : ∫ ω, (G.ξ i ω) ^ 4 ∂P ≤ C ^ 4 := by
  simpa using G.integral_xi_even_le (P := P) i (hC i) 2
include hℱ h_adapt hC0 hC in
/-- The second moment of a partial sum is at most `C²` times the elapsed time. -/
theorem integral_partialSum_sq_le : ∀ (k : ℕ) (hk : k ≤ G.N),
    ∫ ω, (G.partialSum W k ω) ^ 2 ∂P
      ≤ C ^ 2 * G.partition ⟨k, Nat.lt_succ_of_le hk⟩ := by
  intro k
  induction k with
  | zero =>
    intro hk
    have h0 : ∀ ω, G.partialSum W 0 ω = 0 := G.partialSum_zero W
    have hp : G.partition (⟨0, Nat.lt_succ_of_le hk⟩ : Fin (G.N + 1)) = 0 := G.partition_zero
    simp_rw [h0]
    simp [G.partition_zero]
  | succ n ih =>
    intro hk
    have hn : n < G.N := hk
    have hΔ0 : (0 : ℝ) ≤ G.partition (⟨n, hn⟩ : Fin G.N).succ
        - G.partition (⟨n, hn⟩ : Fin G.N).castSucc :=
      sub_nonneg.mpr (G.partition_strictMono Fin.castSucc_lt_succ).le
    have he1 : G.partition (⟨n, hn⟩ : Fin G.N).castSucc
        = G.partition (⟨n, Nat.lt_succ_of_le hn.le⟩ : Fin (G.N + 1)) := rfl
    have he2 : G.partition (⟨n, hn⟩ : Fin G.N).succ
        = G.partition (⟨n + 1, Nat.lt_succ_of_le hk⟩ : Fin (G.N + 1)) := rfl
    rw [G.integral_partialSum_sq_succ W ℱ hℱ h_adapt hC0 hC hn]
    have h1 := ih hn.le
    have h2 := G.integral_xi_sq_le (P := P) hC ⟨n, hn⟩
    have h3 := mul_le_mul_of_nonneg_right h2 hΔ0
    rw [he1, he2] at h3 hΔ0 ⊢
    linarith
end Moments

end SimplePredictable

end LevyStochCalc.Brownian.Ito


