-- Prove2me | Definitions.Def_SourceProof_b318e5fb0469045362086285
-- name    : SourceProof_b318e5fb0469045362086285
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:57:50.50986+00:00
-- url     : https://prove2.me/theorems/1a666421-552c-4d06-9b43-d815d0521cad
-- title:
--   LevyStochCalc source module: SourceProof_b318e5fb0469045362086285
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.integral_partialSum_pow_four_le` comes from the `LevyStochCalc.Brownian.ItoFourthMomentPartialSums` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Batteries.Tactic.OpenPrivate
import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F001
import Definitions.Def_SourceProof_b06be9067e73cc8035f80a45

open private integrable_pow_of_memLp from Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F000
open private LevyStochCalc.Brownian.Ito.SimplePredictable.integral_xi_pow_four_le integral_xi_pow_four_le from Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F001
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

theorem _root_.Prove2MeSourceProof.h_b318e5fb0469045362086285 : ∀ (k : ℕ) (hk : k ≤ G.N),
    ∫ ω, (G.partialSum W k ω) ^ 4 ∂P
      ≤ 6 * C ^ 4 * (G.partition (Fin.last G.N)
          * G.partition ⟨k, Nat.lt_succ_of_le hk⟩)
        + gaussianFourthMoment * C ^ 4 * G.partition ⟨k, Nat.lt_succ_of_le hk⟩ ^ 2 := by
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
    -- the mixed second moment
    have hSint : Integrable (fun ω => (G.partialSum W n ω) ^ 2) P :=
      integrable_pow_of_memLp (m := 2) (by norm_num) (by simp)
        (G.memLp_partialSum W hC 2 (by simp) n)
    have hmix : Integrable
        (fun ω => (G.partialSum W n ω) ^ 2 * (G.ξ ⟨n, hn⟩ ω) ^ 2) P := by
      refine (hSint.const_mul (C ^ 2)).mono
        (((G.measurable_partialSum W n).pow_const 2).mul
          ((G.ξ_measurable _).pow_const 2)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      have hx := hC ⟨n, hn⟩ ω
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ C ^ 2)]
      have h4 : |G.ξ ⟨n, hn⟩ ω| ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hx 2
      nlinarith [pow_nonneg (abs_nonneg (G.partialSum W n ω)) 2]
    have hmix_le : ∫ ω, (G.partialSum W n ω) ^ 2 * (G.ξ ⟨n, hn⟩ ω) ^ 2 ∂P
        ≤ C ^ 2 * ∫ ω, (G.partialSum W n ω) ^ 2 ∂P := by
      have hstep : ∫ ω, (G.partialSum W n ω) ^ 2 * (G.ξ ⟨n, hn⟩ ω) ^ 2 ∂P
          ≤ ∫ ω, C ^ 2 * (G.partialSum W n ω) ^ 2 ∂P :=
        integral_mono hmix (hSint.const_mul _) fun ω => by
          have hx := hC ⟨n, hn⟩ ω
          have h4 : |G.ξ ⟨n, hn⟩ ω| ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hx 2
          have h5 : (G.ξ ⟨n, hn⟩ ω) ^ 2 ≤ C ^ 2 := by
            rwa [← abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (G.ξ ⟨n, hn⟩ ω) ^ 2)] at h4
          nlinarith [sq_nonneg (G.partialSum W n ω)]
      rwa [integral_const_mul] at hstep
    have hS2 := G.integral_partialSum_sq_le W ℱ hℱ h_adapt hC0 hC n hn.le
    have hlast : G.partition (⟨n, Nat.lt_succ_of_le hn.le⟩ : Fin (G.N + 1))
        ≤ G.partition (Fin.last G.N) :=
      G.partition_strictMono.monotone (by rw [Fin.le_def]; simp [Fin.last]; omega)
    have hτ0 : (0 : ℝ) ≤ G.partition (⟨n, Nat.lt_succ_of_le hn.le⟩ : Fin (G.N + 1)) :=
      G.partition_nonneg _
    have hc0 : (0 : ℝ) ≤ LevyStochCalc.Brownian.Ito.gaussianFourthMoment := LevyStochCalc.Brownian.Ito.gaussianFourthMoment_nonneg
    have hξ4 := G.integral_xi_pow_four_le (P := P) hC ⟨n, hn⟩
    rw [(_root_.Prove2MeSourceProof.h_b06be9067e73cc8035f80a45 G) W ℱ hℱ h_adapt hC0 hC hn]
    have h1 := ih hn.le
    rw [he1, he2] at hΔ0 ⊢
    nlinarith [mul_nonneg (pow_nonneg hC0 4) hΔ0, sq_nonneg C,
      mul_nonneg hc0 (mul_nonneg (pow_nonneg hC0 4) (mul_nonneg hτ0 hΔ0)),
      mul_le_mul_of_nonneg_right hmix_le hΔ0,
      mul_le_mul_of_nonneg_right hS2 hΔ0,
      mul_le_mul_of_nonneg_right hξ4
        (mul_nonneg (mul_nonneg hΔ0 hΔ0) hc0)]
end Moments

end SimplePredictable

end LevyStochCalc.Brownian.Ito


