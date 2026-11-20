-- Prove2me | Definitions.Def_SourceProof_a0fdf743e5bf870d245cbc9c
-- name    : SourceProof_a0fdf743e5bf870d245cbc9c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T11:01:49.15133+00:00
-- url     : https://prove2.me/theorems/12db58a0-af01-49ae-b320-43b05c2ca5ba
-- title:
--   LevyStochCalc source module: SourceProof_a0fdf743e5bf870d245cbc9c
-- statement:
--   The original source theorem `ProbabilityTheory.integral_sum_weight_increments_mem_Icc` comes from the `BrownianMotion.StochasticIntegral.Quasimartingale.MaximalInequality` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_MaximalInequality_F001

/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohit Manokaran, Rémy Degenne
-/

/-! # Maximal inequality for real quasimartingales -/

@[expose] public section

open MeasureTheory Finset Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory.SimpleProcess

namespace ProbabilityTheory

variable {ι Ω : Type*} [LinearOrder ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}
  {X : ι → Ω → ℝ} {τ σ : Ω → WithTop ι} {i : ι}

section Bridge

variable {F : Finset ι} {t : ι} {k l : ℕ}

end Bridge

/-! ### Upcrossing and alternation bounds along finite time sets -/

section UpcrossingBound

variable {a b : ℝ} {t : ι} {F : Finset ι} {m : ℕ}

end UpcrossingBound

/-! ### Selection of alternating tuples from frequent oscillation -/

section Selection

variable [TopologicalSpace ι] [OrderTopology ι]

variable {T : Set ι} {x d : ι} {a b : ℝ} {ω : Ω}

end Selection

/-! ### Maximal inequality along finite time sets -/

section Maximal

variable {t : ι} {F : Finset ι} {lam : ℝ}

-- todo name


theorem _root_.Prove2MeSourceProof.h_a0fdf743e5bf870d245cbc9c [OrderBot ι]
    (hXint : ∀ s, Integrable (X s) μ) {C : ℝ}
    (hC : ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C)
    {n : ℕ} {idx : ℕ → ι} (hidx : Monotone idx) (hidxt : ∀ k, idx k ≤ t)
    {W : ℕ → Ω → ℝ} (hW01 : ∀ k, k < n → ∀ ω, W k ω = 0 ∨ W k ω = 1)
    (hWmeas : ∀ k, k < n → Measurable[𝓕 (idx k)] (W k)) :
    ∫ ω, (∑ k ∈ range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω)) ∂μ
        ∈ Set.Icc (-(C + ∫ ω, |X (idx n) ω - X (idx 0) ω| ∂μ)) C := by
  have hb01 : ∀ (V : ℕ → Ω → ℝ), (∀ k, k < n → ∀ ω, V k ω = 0 ∨ V k ω = 1) →
      ∀ k, k < n → ∀ ω, ‖V k ω‖ ≤ 1 := by
    intro V hV k hk ω
    rcases hV k hk ω with h | h <;> simp [h]
  have hupper : ∀ (V : ℕ → Ω → ℝ), (∀ k, k < n → ∀ ω, V k ω = 0 ∨ V k ω = 1) →
      (∀ k, k < n → Measurable[𝓕 (idx k)] (V k)) →
      ∫ ω, (∑ k ∈ range n, V k ω * (X (idx (k + 1)) ω - X (idx k) ω)) ∂μ ≤ C := by
    intro V hV01 hVmeas
    let S := ProbabilityTheory.elemPredSetOfSeq hidx n hVmeas
    have hS := _root_.Prove2MeSourceProof.h_c62814fa18df3f1630c0e9da (𝓕 := 𝓕) (X := X) n hidx hidxt (W := V) hV01 hVmeas
    rw [← funext_iff] at hS
    rw [← hS]
    exact hC S
  constructor
  · -- lower bound via the complementary weights
    have hW1 : ∀ k, k < n → ∀ ω, (1 - W k ω) = 0 ∨ (1 - W k ω) = 1 := by grind
    have hW1meas : ∀ k, k < n → Measurable[𝓕 (idx k)] (fun ω ↦ 1 - W k ω) :=
      fun k hk ↦ (measurable_const.sub (hWmeas k hk))
    have hco := hupper (fun k ω ↦ 1 - W k ω) hW1 hW1meas
    have hsplit : ∀ ω, (∑ k ∈ range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω))
        = (X (idx n) ω - X (idx 0) ω)
          - ∑ k ∈ range n, (1 - W k ω) * (X (idx (k + 1)) ω - X (idx k) ω) := by
      intro ω
      have htel : ∑ k ∈ range n, (X (idx (k + 1)) ω - X (idx k) ω)
          = X (idx n) ω - X (idx 0) ω := sum_range_sub (fun k ↦ X (idx k) ω) n
      rw [← htel, ← sum_sub_distrib]
      grind
    have hint1 : Integrable
        (fun ω ↦ ∑ k ∈ range n, (1 - W k ω) * (X (idx (k + 1)) ω - X (idx k) ω)) μ :=
      ProbabilityTheory.integrable_sum_weight_increments hXint
        (fun k hk ↦ ((hW1meas k hk).mono (𝓕.le _) le_rfl).aestronglyMeasurable)
        (hb01 _ hW1)
    have hintsub : Integrable (fun ω ↦ X (idx n) ω - X (idx 0) ω) μ :=
      (hXint _).sub (hXint _)
    have hI : ∫ ω, (∑ k ∈ range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω)) ∂μ
        = (∫ ω, (X (idx n) ω - X (idx 0) ω) ∂μ)
          - ∫ ω, (∑ k ∈ range n, (1 - W k ω) * (X (idx (k + 1)) ω - X (idx k) ω)) ∂μ := by
      rw [integral_congr_ae (μ := μ) (ae_of_all _ hsplit), integral_sub hintsub hint1]
    have hT : -(∫ ω, |X (idx n) ω - X (idx 0) ω| ∂μ)
        ≤ ∫ ω, (X (idx n) ω - X (idx 0) ω) ∂μ := by
      rw [neg_le]
      calc -∫ ω, (X (idx n) ω - X (idx 0) ω) ∂μ
          ≤ |∫ ω, (X (idx n) ω - X (idx 0) ω) ∂μ| := neg_le_abs _
        _ ≤ ∫ ω, |X (idx n) ω - X (idx 0) ω| ∂μ := abs_integral_le_integral_abs
    rw [hI]
    linarith [hco]
  · exact hupper W hW01 hWmeas
end Maximal

/-! ## Maximal inequality for countable sets -/

section CountableEvents

variable {T : Set ι} {t : ι} {a b lam : ℝ} {m : ℕ}

variable [OrderBot ι]

end CountableEvents

end ProbabilityTheory


