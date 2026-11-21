-- Prove2me | Definitions.Def_SourceProof_4bba863570ba53ef5f94bc24
-- name    : SourceProof_4bba863570ba53ef5f94bc24
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:01:34.820482+00:00
-- url     : https://prove2.me/theorems/9eb84ff4-6e1c-4792-b848-017a4aa33363
-- title:
--   LevyStochCalc source module: SourceProof_4bba863570ba53ef5f94bc24
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.integral_partialSum_pow_four_le_varClock` comes from the `LevyStochCalc.Brownian.ItoFourthMomentPartialSums` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F002
import Definitions.Def_SourceProof_746d4755a7cc9a561814f282
import Definitions.Def_SourceProof_b06be9067e73cc8035f80a45

open private integrable_pow_of_memLp from Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F000
open private LevyStochCalc.Brownian.Ito.SimplePredictable.integral_xi_even_le integral_xi_even_le from Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F001
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

theorem _root_.Prove2MeSourceProof.h_4bba863570ba53ef5f94bc24 {c : Fin G.N → ℝ}
    (hc : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ c i) :
    ∀ (k : ℕ) (_hk : k ≤ G.N),
      ∫ ω, (G.partialSum W k ω) ^ 4 ∂P
        ≤ 6 * (G.varClock c G.N * G.varClock c k)
          + gaussianFourthMoment * G.varClock c k ^ 2 := by
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
    have hcn2 : (0 : ℝ) ≤ c ⟨n, hn⟩ ^ 2 := sq_nonneg _
    have hxi2 : ∀ ω, (G.ξ ⟨n, hn⟩ ω) ^ 2 ≤ c ⟨n, hn⟩ ^ 2 := fun ω => by
      have h := pow_le_pow_left₀ (abs_nonneg (G.ξ ⟨n, hn⟩ ω)) (hc ⟨n, hn⟩ ω) 2
      rwa [← abs_pow, abs_of_nonneg (sq_nonneg (G.ξ ⟨n, hn⟩ ω))] at h
    have hSint : Integrable (fun ω => (G.partialSum W n ω) ^ 2) P :=
      integrable_pow_of_memLp (m := 2) (by norm_num) (by simp)
        (G.memLp_partialSum W hC 2 (by simp) n)
    have hmix : Integrable
        (fun ω => (G.partialSum W n ω) ^ 2 * (G.ξ ⟨n, hn⟩ ω) ^ 2) P := by
      refine (hSint.const_mul (c ⟨n, hn⟩ ^ 2)).mono
        (((G.measurable_partialSum W n).pow_const 2).mul
          ((G.ξ_measurable _).pow_const 2)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow,
        abs_of_nonneg hcn2]
      have h4 : |G.ξ ⟨n, hn⟩ ω| ^ 2 ≤ c ⟨n, hn⟩ ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (hc ⟨n, hn⟩ ω) 2
      nlinarith [pow_nonneg (abs_nonneg (G.partialSum W n ω)) 2]
    have hmix_le : ∫ ω, (G.partialSum W n ω) ^ 2 * (G.ξ ⟨n, hn⟩ ω) ^ 2 ∂P
        ≤ c ⟨n, hn⟩ ^ 2 * ∫ ω, (G.partialSum W n ω) ^ 2 ∂P := by
      have hstep : ∫ ω, (G.partialSum W n ω) ^ 2 * (G.ξ ⟨n, hn⟩ ω) ^ 2 ∂P
          ≤ ∫ ω, c ⟨n, hn⟩ ^ 2 * (G.partialSum W n ω) ^ 2 ∂P :=
        integral_mono hmix (hSint.const_mul _) fun ω => by
          nlinarith [sq_nonneg (G.partialSum W n ω), hxi2 ω]
      rwa [integral_const_mul] at hstep
    have hS2 := G.integral_partialSum_sq_le_varClock W ℱ hℱ h_adapt hC0 hC hc n hn.le
    have hVN : G.varClock c n ≤ G.varClock c G.N := (_root_.Prove2MeSourceProof.h_746d4755a7cc9a561814f282 G) c hn.le
    have hV0 : (0 : ℝ) ≤ G.varClock c n := G.varClock_nonneg c n
    have hcg : (0 : ℝ) ≤ LevyStochCalc.Brownian.Ito.gaussianFourthMoment := LevyStochCalc.Brownian.Ito.gaussianFourthMoment_nonneg
    have hA : (∫ ω, (G.partialSum W n ω) ^ 2 * (G.ξ ⟨n, hn⟩ ω) ^ 2 ∂P)
        ≤ c ⟨n, hn⟩ ^ 2 * G.varClock c G.N :=
      hmix_le.trans (mul_le_mul_of_nonneg_left (hS2.trans hVN) hcn2)
    have hB : (∫ ω, (G.ξ ⟨n, hn⟩ ω) ^ 4 ∂P) ≤ c ⟨n, hn⟩ ^ 4 := by
      simpa using G.integral_xi_even_le (P := P) ⟨n, hn⟩ (hc ⟨n, hn⟩) 2
    rw [(_root_.Prove2MeSourceProof.h_b06be9067e73cc8035f80a45 G) W ℱ hℱ h_adapt hC0 hC hn, G.varClock_succ c hn]
    have h1 := ih hn.le
    nlinarith [mul_le_mul_of_nonneg_right hA hΔ0,
      mul_le_mul_of_nonneg_right hB
        (mul_nonneg (mul_nonneg hΔ0 hΔ0) hcg),
      mul_nonneg (mul_nonneg (mul_nonneg hcg hV0) hcn2) hΔ0]
end Moments

end SimplePredictable

end LevyStochCalc.Brownian.Ito


