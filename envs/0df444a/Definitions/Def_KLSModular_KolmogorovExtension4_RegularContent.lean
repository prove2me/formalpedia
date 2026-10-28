-- Prove2me | Definitions.Def_KLSModular_KolmogorovExtension4_RegularContent
-- name    : KLSModular_KolmogorovExtension4_RegularContent
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:37:14.844935+00:00
-- url     : https://prove2.me/theorems/f5d12dbc-795b-458a-87bd-4311f5712fc8
-- title:
--   Regularity criteria for countable additivity of contents
-- statement:
--   Vendored from the KolmogorovExtension4 library, repository https://github.com/RemyDegenne/kolmogorov_extension4, commit f33cbc388e5d444606dffa7eec507a26b62c15bb. The lemma `tendsto_zero_of_regular_addContent` states that if an ℝ≥0∞-valued `AddContent` on a set ring is regular with respect to a compact system, then its values on an antitone sequence of ring sets with empty intersection tend to 0 at infinity. The lemma `addContent_iUnion_eq_sum_of_regular` consequently identifies the content of a countable pairwise disjoint union with the ∑'-sum of the individual contents, assuming finite values on the ring, regularity, and membership of both the union and its pieces.
--
--   **Original module imports**
--
--   ```lean
--   public import KolmogorovExtension4.CompactSystem
--   public import Mathlib.MeasureTheory.Measure.AddContent
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context. Body omitted.
--
--   ```lean
--   lemma tendsto_zero_of_regular_addContent (hR : IsSetRing R) (m : AddContent ℝ≥0∞ R)
--       (hs : ∀ n, s n ∈ R) (hs_anti : Antitone s) (hs_Inter : (⋂ n, s n) = ∅)
--       (hC : IsCompactSystem C) (hCR : C ⊆ R)
--       (h_reg : ∀ A (_ : A ∈ R) (ε : ℝ≥0∞) (_ : 0 < ε), ∃ K ∈ C, K ⊆ A ∧ m (A \ K) ≤ ε) :
--       Filter.Tendsto (fun n ↦ m (s n)) Filter.atTop (nhds 0)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KolmogorovExtension4/CompactSystem`](https://prove2.me/theorems/cc892fdb-6ea2-43bd-9fa8-b2e4772c8674).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/KolmogorovExtension4/KolmogorovExtension4/RegularContent.lean) · `KolmogorovExtension4.RegularContent` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/RemyDegenne/kolmogorov_extension4/blob/f33cbc388e5d444606dffa7eec507a26b62c15bb/KolmogorovExtension4/RegularContent.lean#L21-L81 (repository human-ai-mathematics/kls-lean, commit 408915f, module `KolmogorovExtension4.RegularContent`, definition bundle `KLSModular_KolmogorovExtension4_RegularContent`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/kolmogorov_extension4 at commit f33cbc388e5d444606dffa7eec507a26b62c15bb (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_KolmogorovExtension4_CompactSystem
import Mathlib.MeasureTheory.Measure.AddContent

/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
-- Vendored from https://github.com/RemyDegenne/kolmogorov_extension4 at commit f33cbc388e5d444606dffa7eec507a26b62c15bb (upstream path KolmogorovExtension4/RegularContent.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open scoped ENNReal
namespace MeasureTheory
variable {α : Type*} {C R : Set (Set α)} {s : ℕ → Set α}
lemma tendsto_zero_of_regular_addContent (hR : IsSetRing R) (m : AddContent ℝ≥0∞ R)
    (hs : ∀ n, s n ∈ R) (hs_anti : Antitone s) (hs_Inter : (⋂ n, s n) = ∅)
    (hC : IsCompactSystem C) (hCR : C ⊆ R)
    (h_reg : ∀ A (_ : A ∈ R) (ε : ℝ≥0∞) (_ : 0 < ε), ∃ K ∈ C, K ⊆ A ∧ m (A \ K) ≤ ε) :
    Filter.Tendsto (fun n ↦ m (s n)) Filter.atTop (nhds 0) := by
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [Set.eq_empty_of_isEmpty]
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ_sum⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' ℕ
  have h_reg' : ∀ n, ∃ K ∈ C, K ⊆ s n ∧ m (s n \ K) ≤ δ n :=
    fun n ↦ h_reg (s n) (hs n) (δ n) (mod_cast (hδ_pos n))
  choose t ht_mem_C ht_subset ht using h_reg'
  rw [Filter.eventually_atTop]
  have ht_empty : ⋂ n, t n = ∅ := Set.subset_eq_empty (Set.iInter_mono ht_subset) hs_Inter
  let S := hC.support ht_mem_C ht_empty
  have hS := hC.iInter_eq_empty ht_mem_C ht_empty
  have hS_nonempty : Finset.Nonempty (Finset.Iic S) := by simp
  let N := Finset.max' (Finset.Iic S) hS_nonempty
  have ht_empty' : ∀ n, N ≤ n → ⋂ i ≤ n, t i = ∅ := by
    intro n hn
    refine Set.subset_eq_empty ?_ hS
    simp only [Set.subset_iInter_iff]
    intro i hi
    refine Set.biInter_subset_of_mem ?_
    exact (Finset.le_max' (Finset.Iic S) i (by simpa using hi)).trans hn
  refine ⟨N, fun n hn ↦ ?_⟩
  calc m (s n) = m (⋂ i ≤ n, s i) := by
        congr
        exact le_antisymm (le_iInf₂ fun i hi ↦ hs_anti hi)
          (iInf₂_le (κ := fun i ↦ i ≤ n) (f := fun i _ ↦ s i) n le_rfl)
    _ = m ((⋂ i ≤ n, s i) \ (⋂ i ≤ n, t i)) := by simp only [ht_empty' n hn, Set.sdiff_empty]
    _ ≤ m (⋃ i ≤ n, (s i \ t i)) := by
        refine addContent_mono hR.isSetSemiring ?_ ?_ ?_
        · exact hR.sdiff_mem (hR.iInter_le_mem hs n) (hR.iInter_le_mem (fun i ↦ hCR (ht_mem_C i)) n)
        · exact hR.iUnion_le_mem (fun i ↦ hR.sdiff_mem (hs i) (hCR (ht_mem_C i))) n
        · rw [Set.sdiff_iInter]
          refine Set.iUnion_mono (fun i ↦ ?_)
          by_cases hin : i ≤ n
          · simp only [hin, Set.iInter_true, Set.iUnion_true]
            refine Set.sdiff_subset_sdiff ?_ subset_rfl
            exact Set.biInter_subset_of_mem hin
          · simp only [hin, Set.iInter_of_empty, Set.sdiff_univ, Set.iUnion_of_empty,
              Set.empty_subset]
    _ = m (⋃ i ∈ Finset.range (n + 1), (s i \ t i)) := by simp only [Finset.mem_range_succ_iff]
    _ ≤ ∑ i ∈ Finset.range (n + 1), m (s i \ t i) :=
        addContent_biUnion_le hR (fun i _ ↦ hR.sdiff_mem (hs i) (hCR (ht_mem_C i)))
    _ ≤ ∑ i ∈ Finset.range (n + 1), (δ i : ℝ≥0∞) := Finset.sum_le_sum (fun i _ ↦ ht i)
    _ ≤ ∑' i, (δ i : ℝ≥0∞) := ENNReal.sum_le_tsum _
    _ ≤ ε := hδ_sum.le
lemma addContent_iUnion_eq_sum_of_regular (hR : IsSetRing R) (m : AddContent ℝ≥0∞ R)
    (hm_ne_top : ∀ s ∈ R, m s ≠ ∞)
    (hC : IsCompactSystem C) (hCR : C ⊆ R)
    (h_reg : ∀ A ∈ R, ∀ ε, 0 < ε → ∃ K ∈ C, K ⊆ A ∧ m (A \ K) ≤ ε)
    ⦃f : ℕ → Set α⦄ (hf : ∀ i, f i ∈ R) (hUf : (⋃ i, f i) ∈ R)
    (h_disj : Pairwise (Function.onFun Disjoint f)) :
    m (⋃ i, f i) = ∑' i, m (f i) := by
  refine addContent_iUnion_eq_sum_of_tendsto_zero hR m hm_ne_top ?_ hf hUf h_disj
  intro s hs hs_anti hs_iInter
  exact tendsto_zero_of_regular_addContent hR m hs hs_anti hs_iInter hC hCR h_reg
end MeasureTheory


