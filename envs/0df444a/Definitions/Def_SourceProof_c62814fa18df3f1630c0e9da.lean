-- Prove2me | Definitions.Def_SourceProof_c62814fa18df3f1630c0e9da
-- name    : SourceProof_c62814fa18df3f1630c0e9da
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:44:37.043434+00:00
-- url     : https://prove2.me/theorems/126a37aa-ae34-400d-99b9-dd600fa240c6
-- title:
--   LevyStochCalc source proof: ProbabilityTheory.integral_elemPredSetOfSeq
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_MaximalInequality_F000

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

theorem _root_.Prove2MeSourceProof.h_c62814fa18df3f1630c0e9da [OrderBot ι] {t : ι} (n : ℕ) {idx : ℕ → ι}
    (hidx : Monotone idx) (hidxt : ∀ k, idx k ≤ t) {W : ℕ → Ω → ℝ}
    (hW01 : ∀ k, k < n → ∀ ω, W k ω = 0 ∨ W k ω = 1)
    (hWmeas : ∀ k, k < n → Measurable[𝓕 (idx k)] (W k)) (ω : Ω) :
    ((elemPredSetOfSeq hidx n hWmeas).indicator (1 : ℝ) ● X) t ω =
      ∑ k ∈ range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω) := by
  let K : Finset ℕ := {k ∈ range n | idx k < idx (k + 1)}
  have hKmem : ∀ {k}, k ∈ K → k < n ∧ idx k < idx (k + 1) := by
    intro k hk
    simpa [K] using hk
  have hinj : Set.InjOn (fun k ↦ (idx k, idx (k + 1))) K := by
    intro k hk l hl hkl
    simp only [Prod.mk.injEq] at hkl
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact absurd ((hidx (Nat.succ_le_of_lt h)).trans_eq hkl.1.symm) (hKmem hk).2.not_ge
    · exact absurd ((hidx (Nat.succ_le_of_lt h)).trans_eq hkl.1) (hKmem hl).2.not_ge
  rw [ProbabilityTheory.ElementaryPredictableSet.integral_indicator_apply]
  simp only [ProbabilityTheory.elemPredSetOfSeq_I, ProbabilityTheory.elemPredSetOfSeq_set]
  simp only [mem_filter, mem_range, ContinuousLinearMap.mul_apply', one_mul]
  rw [sum_image fun k hk l hl h ↦ hinj hk hl h]
  simp only [mem_filter, mem_range, Prod.mk.injEq]
  refine (sum_congr rfl fun k hk ↦ ?_).trans (sum_subset (filter_subset _ _) fun k hk hkK ↦ ?_)
  · -- per-term equality on K
    have h : ∃ k_1 ∈ {k ∈ range n | idx k < idx (k + 1)},
      (idx k_1, idx (k_1 + 1)) = (idx k, idx (k + 1)) := ⟨k, hk, rfl⟩
    rw [dif_pos h]
    suffices (W h.choose ⁻¹' {1}).indicator
        (fun ω ↦ stoppedProcess X (fun x ↦ ↑t) (idx (k + 1)) ω -
          stoppedProcess X (fun x ↦ ↑t) (idx k) ω) ω =
        W k ω * (X (idx (k + 1)) ω - X (idx k) ω) by
      convert this
      · rfl
      · simp
      · simp
    have hchoose : h.choose = k := hinj h.choose_spec.1 hk h.choose_spec.2
    have hst : ∀ j, stoppedProcess X (fun _ ↦ (t : WithTop ι)) (idx j) ω = X (idx j) ω :=
      fun j ↦ stoppedProcess_eq_of_le (mod_cast hidxt j)
    simp only [hchoose]
    rcases hW01 k (hKmem hk).1 ω with h0 | h1
    · simp [h0]
    · simp [h1, hst]
  · -- terms outside K vanish
    have hno : ¬ idx k < idx (k + 1) := fun h ↦ hkK (by simp [K, mem_range.1 hk, h])
    have heq : idx (k + 1) = idx k :=
      le_antisymm (not_lt.1 hno) (hidx k.le_succ)
    rw [heq, sub_self, mul_zero]
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

end Maximal

/-! ## Maximal inequality for countable sets -/

section CountableEvents

variable {T : Set ι} {t : ι} {a b lam : ℝ} {m : ℕ}

variable [OrderBot ι]

end CountableEvents

end ProbabilityTheory


