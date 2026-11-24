-- Prove2me | Definitions.Def_SourceProof_eae059fb1d843e68f8ce3b08
-- name    : SourceProof_eae059fb1d843e68f8ce3b08
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:17:15.029034+00:00
-- url     : https://prove2.me/theorems/7c4bf7eb-dc37-4b6d-a3bb-995675ac0a79
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.discreteStochasticIntegral

import Definitions.Def_StochLean_Probability_Martingale_DiscreteIntegral_F000
import Definitions.Def_SourceProof_12c6e978969ea0272068034a
import Definitions.Def_SourceProof_72e355a9b50999c17ffa8bc4

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Discrete stochastic integrals

This file gives a named API for the discrete predictable transform

`(H · X) n = ∑ k ∈ range n, H (k + 1) • (X (k + 1) - X k)`.

The `k + 1` convention is deliberate: predictability says that `H (k + 1)` is
measurable with respect to the information available at time `k`.
-/

@[expose] public section

open scoped BigOperators

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω}

section Martingale

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} {𝓕 : Filtration ℕ mΩ} {H : ℕ → Ω → ℝ} {X : ℕ → Ω → E}

namespace Martingale

theorem _root_.Prove2MeSourceProof.h_eae059fb1d843e68f8ce3b08 [IsFiniteMeasure μ]
    (hX : Martingale X 𝓕 μ) (hH : IsStronglyPredictable 𝓕 H)
    (hH_bdd : ∀ n, ∃ C : ℝ, ∀ᵐ ω ∂μ, ‖H n ω‖ ≤ C) :
    Martingale (MeasureTheory.discreteStochasticIntegral H X) 𝓕 μ := by
  choose C hC using hH_bdd
  have hint : ∀ n, Integrable (MeasureTheory.discreteStochasticIntegral H X n) μ := by
    intro n
    rw [_root_.Prove2MeSourceProof.h_12c6e978969ea0272068034a]
    exact integrable_finsetSum' _ fun k _ => Integrable.bdd_smul
      ((hX.integrable (k + 1)).sub (hX.integrable k)) (C (k + 1))
      ((hH.measurable_add_one k).mono (𝓕.le k)).aestronglyMeasurable (hC (k + 1))
  have hadp : StronglyAdapted 𝓕 (MeasureTheory.discreteStochasticIntegral H X) := by
    intro n
    rw [_root_.Prove2MeSourceProof.h_12c6e978969ea0272068034a]
    refine Finset.stronglyMeasurable_sum _ fun k hk => ?_
    rw [Finset.mem_range] at hk
    exact ((hH.measurable_add_one k).mono (𝓕.mono hk.le)).smul
      (((hX.stronglyMeasurable (k + 1)).mono (𝓕.mono (Nat.succ_le_of_lt hk))).sub
        ((hX.stronglyMeasurable k).mono (𝓕.mono hk.le)))
  refine martingale_of_condExp_sub_eq_zero_nat hadp hint fun n => ?_
  have hdiff : MeasureTheory.discreteStochasticIntegral H X (n + 1) -
      MeasureTheory.discreteStochasticIntegral H X n =
        H (n + 1) • (X (n + 1) - X n) := by
    rw [_root_.Prove2MeSourceProof.h_72e355a9b50999c17ffa8bc4]
    abel
  rw [hdiff]
  calc
    μ[H (n + 1) • (X (n + 1) - X n) | 𝓕 n] =ᵐ[μ]
        H (n + 1) • μ[X (n + 1) - X n | 𝓕 n] :=
      condExp_smul_of_aestronglyMeasurable_left
        (hH.measurable_add_one n).aestronglyMeasurable
        (((hX.integrable (n + 1)).sub (hX.integrable n)).bdd_smul (C (n + 1))
          ((hH.measurable_add_one n).mono (𝓕.le n)).aestronglyMeasurable (hC (n + 1)))
        ((hX.integrable (n + 1)).sub (hX.integrable n))
    _ =ᵐ[μ] H (n + 1) • 0 := by
      have hΔ : μ[X (n + 1) - X n | 𝓕 n] =ᵐ[μ] 0 := by
        calc
          μ[X (n + 1) - X n | 𝓕 n] =ᵐ[μ]
              μ[X (n + 1) | 𝓕 n] - μ[X n | 𝓕 n] :=
            condExp_sub (hX.integrable (n + 1)) (hX.integrable n) _
          _ =ᵐ[μ] X n - X n :=
            (hX.condExp_ae_eq n.le_succ).sub (hX.condExp_ae_eq le_rfl)
          _ =ᵐ[μ] 0 := by simp
      filter_upwards [hΔ] with ω hω
      simp [hω]
    _ = 0 := by simp
end Martingale

end Martingale

end MeasureTheory


