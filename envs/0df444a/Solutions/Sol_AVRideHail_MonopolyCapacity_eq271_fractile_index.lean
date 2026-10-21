-- Prove2me | solution 1 for AVRideHail.MonopolyCapacity.eq271_fractile_index
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:15:51.333005+00:00
-- url     : https://prove2.me/submissions/a2183a86-b759-4abe-b132-5c8c3a14fa15

import Mathlib
import Definitions.Def_AVRideHail_MonopolyCapacity_Model
set_option autoImplicit false
open AVRideHail.MonopolyCapacity

theorem solution (I : ℕ) (hI : 0 < I) (prob : Fin I → ℝ)
    (hprob : ∀ i, 0 ≤ prob i) (hsum : ∑ i, prob i = 1) (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    (∃! K : Fin I, ∑ j ∈ Finset.Ioi K, prob j < c ∧ c ≤ ∑ j ∈ Finset.Ici K, prob j) ∧
      ∀ K : Fin I, IsLeast {k : Fin I | ∑ j ∈ Finset.Ioi k, prob j < c} K →
        (∑ j ∈ Finset.Ioi K, prob j < c ∧ c ≤ ∑ j ∈ Finset.Ici K, prob j) := by
  have hleast : ∀ K : Fin I, IsLeast {k : Fin I | ∑ j ∈ Finset.Ioi k, prob j < c} K →
        (∑ j ∈ Finset.Ioi K, prob j < c ∧ c ≤ ∑ j ∈ Finset.Ici K, prob j) := by
    intro K hK
    refine ⟨hK.1, ?_⟩
    by_cases h0 : K.val = 0
    · have hK0 : K = ⟨0, hI⟩ := Fin.ext h0
      have : Finset.Ici K = Finset.univ := by
        ext i; simp only [Finset.mem_Ici, Finset.mem_univ, iff_true]
        rw [Fin.le_def]; omega
      rw [this, hsum]; exact hc1.le
    · have hpos : 0 < K.val := Nat.pos_of_ne_zero h0
      let K' : Fin I := ⟨K.val - 1, by omega⟩
      have hnot : ¬ (∑ j ∈ Finset.Ioi K', prob j < c) := by
        intro hlt
        have := hK.2 hlt
        rw [Fin.le_def] at this
        simp only [K'] at this
        omega
      have : Finset.Ioi K' = Finset.Ici K := by
        ext i; simp only [Finset.mem_Ioi, Finset.mem_Ici, Fin.lt_def, Fin.le_def, K']
        omega
      rw [this] at hnot
      exact not_lt.mp hnot
  have hne : (Finset.univ.filter (fun k : Fin I => ∑ j ∈ Finset.Ioi k, prob j < c)).Nonempty := by
    refine ⟨⟨I - 1, by omega⟩, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have : Finset.Ioi (⟨I - 1, by omega⟩ : Fin I) = ∅ := by
      ext i; simp only [Finset.mem_Ioi, Finset.notMem_empty, iff_false, Fin.lt_def]
      have := i.isLt; omega
    rw [this]; simpa using hc0
  obtain ⟨K, hK⟩ : ∃ K, IsLeast {k : Fin I | ∑ j ∈ Finset.Ioi k, prob j < c} K := by
    refine ⟨(Finset.univ.filter (fun k : Fin I => ∑ j ∈ Finset.Ioi k, prob j < c)).min' hne, ?_, ?_⟩
    · have := Finset.min'_mem _ hne
      simpa using this
    · intro k hk
      exact Finset.min'_le _ k (by simpa using hk)
  refine ⟨⟨K, hleast K hK, ?_⟩, hleast⟩
  intro K2 ⟨h2a, h2b⟩
  have hsub : ∀ A B : Fin I, A < B → c ≤ ∑ j ∈ Finset.Ici B, prob j → ¬ (∑ j ∈ Finset.Ioi A, prob j < c) := by
    intro A B hAB hB hlt
    have : ∑ j ∈ Finset.Ici B, prob j ≤ ∑ j ∈ Finset.Ioi A, prob j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        simp only [Finset.mem_Ici, Finset.mem_Ioi] at hi ⊢
        exact lt_of_lt_of_le hAB hi
      · intro i _ _; exact hprob i
    linarith
  have hK1 := hleast K hK
  rcases lt_trichotomy K2 K with h | h | h
  · exact absurd h2a (hsub K2 K h hK1.2)
  · exact h
  · exact absurd hK1.1 (hsub K K2 h h2b)
