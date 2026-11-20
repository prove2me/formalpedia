-- Prove2me | Definitions.Def_SourceProof_43f1d351fc8089295565fd5b
-- name    : SourceProof_43f1d351fc8089295565fd5b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T12:27:18.577179+00:00
-- url     : https://prove2.me/theorems/5eb55b6a-7b57-408d-906e-fd122fe8e91c
-- title:
--   LevyStochCalc source module: SourceProof_43f1d351fc8089295565fd5b
-- statement:
--   The original source theorem `ProbabilityTheory.measureReal_exists_abs_lt_le` comes from the `BrownianMotion.StochasticIntegral.Quasimartingale.MaximalInequality` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_a05b300f3542b3c3884120f0
import Definitions.Def_SourceProof_a0fdf743e5bf870d245cbc9c

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


theorem _root_.Prove2MeSourceProof.h_43f1d351fc8089295565fd5b [OrderBot ι] [IsFiniteMeasure μ]
    (hX : StronglyAdapted 𝓕 X) (hXint : ∀ s, Integrable (X s) μ) {C : ℝ}
    (hC : ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C)
    (hlam : 0 < lam) (hF : ∀ s ∈ F, s ≤ t) :
    μ.real {ω | ∃ s ∈ F, lam < |X s ω|}
      ≤ 2 * (C + ∫ ω, |X t ω - X ⊥ ω| ∂μ + ∫ ω, |X ⊥ ω| ∂μ + ∫ ω, |X t ω| ∂μ) / lam := by
  set G : Finset ι := insert ⊥ F with hG
  have hGF : F ⊆ G := subset_insert _ _
  have hGle : ∀ s ∈ G, s ≤ t := by simp [G]; grind
  set n : ℕ := G.card with hn
  set idx : ℕ → ι := ProbabilityTheory.finIdx G t with hidx
  have hmono : Monotone idx := ProbabilityTheory.finIdx_monotone hGle
  have hidx0 : idx 0 = ⊥ := ProbabilityTheory.finIdx_zero_eq_bot (mem_insert_self _ _)
  have hidxn : idx n = t := ProbabilityTheory.finIdx_eq_of_card_le hn.ge
  -- two-sided expectation bound for adapted 0/1 weights along `idx`
  have hbdd : ∀ W : ℕ → Ω → ℝ, (∀ k, k < n → ∀ ω, W k ω = 0 ∨ W k ω = 1) →
      (∀ k, k < n → Measurable[𝓕 (idx k)] (W k)) →
      ∫ ω, (∑ k ∈ range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω)) ∂μ
        ∈ Set.Icc (-(C + ∫ ω, |X (idx n) ω - X (idx 0) ω| ∂μ)) C :=
    fun W hW01 hWmeas ↦ _root_.Prove2MeSourceProof.h_a0fdf743e5bf870d245cbc9c (t := t) hXint hC hmono
      (ProbabilityTheory.finIdx_le hGle) hW01 hWmeas
  -- apply the one-sided maximal inequality to `X`
  have hpos := _root_.Prove2MeSourceProof.h_a05b300f3542b3c3884120f0 (lam := lam) hX hXint (n := n) hmono (K := C)
    (fun W hW01 hWmeas ↦ (hbdd W hW01 hWmeas).2)
  -- and to `-X`
  have hnegX : StronglyAdapted 𝓕 (fun s ω ↦ -X s ω) := fun s ↦ (hX s).neg
  have hnegint : ∀ s, Integrable ((fun s ω ↦ -X s ω) s) μ := fun s ↦ (hXint s).neg
  have hneg := _root_.Prove2MeSourceProof.h_a05b300f3542b3c3884120f0 (lam := lam) hnegX hnegint (n := n) hmono
    (K := C + ∫ ω, |X (idx n) ω - X (idx 0) ω| ∂μ)
    (fun W hW01 hWmeas ↦ by
      have h1 := (hbdd W hW01 hWmeas).1
      have h2 : ∫ ω, (∑ k ∈ range n, W k ω * (-X (idx (k + 1)) ω - -X (idx k) ω)) ∂μ
          = -∫ ω, (∑ k ∈ range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω)) ∂μ := by
        rw [← integral_neg]
        congr 1 with ω
        rw [← sum_neg_distrib]
        grind
      rw [h2]
      linarith)
  -- combine the two events
  have hsub : {ω | ∃ s ∈ F, lam < |X s ω|}
      ⊆ {ω | ∃ k ≤ n, lam < X (idx k) ω} ∪ {ω | ∃ k ≤ n, lam < -X (idx k) ω} := by
    rintro ω ⟨s, hs, habs⟩
    obtain ⟨k, hk, hkeq⟩ := ProbabilityTheory.exists_finIdx_eq (t := t) (hGF hs)
    grind
  have habs u : ∫ ω, |(fun s ω ↦ -X s ω) u ω| ∂μ = ∫ ω, |X u ω| ∂μ := by simp
  rw [hidx0, hidxn] at hpos hneg
  rw [habs ⊥, habs t] at hneg
  have hunion : μ.real {ω | ∃ s ∈ F, lam < |X s ω|}
      ≤ μ.real {ω | ∃ k ≤ n, lam < X (idx k) ω} + μ.real {ω | ∃ k ≤ n, lam < -X (idx k) ω} :=
    (measureReal_mono hsub).trans (measureReal_union_le _ _)
  have hI : (0 : ℝ) ≤ ∫ ω, |X t ω - X ⊥ ω| ∂μ := integral_nonneg fun ω ↦ abs_nonneg _
  rw [le_div_iff₀ hlam]
  have hmul : lam * μ.real {ω | ∃ s ∈ F, lam < |X s ω|}
      ≤ lam * (μ.real {ω | ∃ k ≤ n, lam < X (idx k) ω}
        + μ.real {ω | ∃ k ≤ n, lam < -X (idx k) ω}) :=
    mul_le_mul_of_nonneg_left hunion hlam.le
  rw [mul_add] at hmul
  nlinarith [hpos, hneg, hmul]
end Maximal

/-! ## Maximal inequality for countable sets -/

section CountableEvents

variable {T : Set ι} {t : ι} {a b lam : ℝ} {m : ℕ}

variable [OrderBot ι]

end CountableEvents

end ProbabilityTheory


