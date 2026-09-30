-- Prove2me | solution 1 for AssignmentGame.CoreCorners.core_tight_on_optimal_matching
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:08:17.331782+00:00
-- url     : https://prove2.me/submissions/1d625b70-ee1b-4f6d-9f95-96ec87a8a7ad

import Definitions.Def_AssignmentGame_CoreCorners_Game
import Mathlib.Tactic
set_option autoImplicit false
open AssignmentGame.CoreCorners Finset

private theorem worth_nonneg {M N : Type*} [Fintype M] [Fintype N]
    (a : M → N → ℝ) (A : Finset M) (B : Finset N) : 0 ≤ worth a A B := by
  have h := Finset.le_sup' (f := fun P : Finset (M × N) => ∑ p ∈ P, a p.1 p.2) (empty_mem_matchings A B)
  simpa [worth] using h

private theorem core_nonneg {M N : Type*} [Fintype M] [Fintype N]
    (a : M → N → ℝ) (p : (M → ℝ) × (N → ℝ)) (hp : p ∈ core a) :
    (∀ i, 0 ≤ p.1 i) ∧ (∀ j, 0 ≤ p.2 j) := by
  classical
  constructor
  · intro i
    have hi := (worth_nonneg a {i} ∅).trans (hp.2 {i} ∅)
    simpa using hi
  · intro j
    have hj := (worth_nonneg a ∅ {j}).trans (hp.2 ∅ {j})
    simpa using hj


private theorem matching_le_worth {M N : Type*} [Fintype M] [Fintype N]
    (a : M → N → ℝ) (A : Finset M) (B : Finset N) (P : Finset (M × N))
    (hP : IsMatching A B P) : ∑ p ∈ P, a p.1 p.2 ≤ worth a A B := by
  classical
  have hm : P ∈ matchings A B := by simp only [matchings, mem_filter, mem_powerset]; exact ⟨hP.1,hP⟩
  exact Finset.le_sup' (f := fun P : Finset (M × N) => ∑ p ∈ P, a p.1 p.2) hm

private theorem pair_lower {M N : Type*} [Fintype M] [Fintype N]
    (a : M → N → ℝ) (u : M → ℝ) (v : N → ℝ) (huv : (u,v) ∈ core a) (i : M) (j : N) :
    a i j ≤ u i+v j := by
  classical
  have hm : IsMatching {i} {j} {(i,j)} := by simp [IsMatching]
  have h := (matching_le_worth a {i} {j} {(i,j)} hm).trans (huv.2 {i} {j})
  simpa using h

theorem solution {M N : Type*} [Fintype M] [Fintype N]
    (a : M → N → ℝ) (ha : ∀ i j, 0 ≤ a i j)
    (P : Finset (M × N)) (hP : IsMatching Finset.univ Finset.univ P)
    (hopt : ∑ p ∈ P, a p.1 p.2 = worth a Finset.univ Finset.univ)
    (u : M → ℝ) (v : N → ℝ) (huv : (u, v) ∈ core a) :
    (∀ p ∈ P, u p.1 + v p.2 = a p.1 p.2) ∧
    (∀ i : M, (∀ p ∈ P, p.1 ≠ i) → u i = 0) ∧
    (∀ j : N, (∀ p ∈ P, p.2 ≠ j) → v j = 0) := by
  classical
  have hs := huv.1
  have hn := core_nonneg a (u,v) huv
  constructor
  · intro p hp
    have hrest : IsMatching (univ.erase p.1) (univ.erase p.2) (P.erase p) := by
      refine ⟨?_, ?_, ?_⟩
      · intro q hq
        obtain ⟨hqp,hqP⟩ := mem_erase.mp hq
        apply mem_product.mpr
        constructor
        · exact mem_erase.mpr ⟨fun heq => hqp (hP.2.1 q hqP p hp heq), mem_univ _⟩
        · exact mem_erase.mpr ⟨fun heq => hqp (hP.2.2 q hqP p hp heq), mem_univ _⟩
      · intro q hq r hr heq
        exact hP.2.1 q (mem_of_mem_erase hq) r (mem_of_mem_erase hr) heq
      · intro q hq r hr heq
        exact hP.2.2 q (mem_of_mem_erase hq) r (mem_of_mem_erase hr) heq
    have hb := (matching_le_worth a _ _ _ hrest).trans (huv.2 (univ.erase p.1) (univ.erase p.2))
    have hu := Finset.sum_erase_add (s := univ) (f := u) (mem_univ p.1)
    have hv := Finset.sum_erase_add (s := univ) (f := v) (mem_univ p.2)
    have hc := Finset.sum_erase_add (s := P) (f := fun q => a q.1 q.2) hp
    have hl := pair_lower a u v huv p.1 p.2
    linarith
  · constructor
    · intro i hi
      have hm : IsMatching (univ.erase i) univ P := by
        refine ⟨?_,hP.2⟩
        intro q hq
        exact mem_product.mpr ⟨mem_erase.mpr ⟨hi q hq, mem_univ _⟩,mem_univ _⟩
      have hb := (matching_le_worth a _ _ _ hm).trans (huv.2 (univ.erase i) univ)
      have he := Finset.sum_erase_add (s := univ) (f := u) (mem_univ i)
      have hi0 := hn.1 i
      linarith
    · intro j hj
      have hm : IsMatching univ (univ.erase j) P := by
        refine ⟨?_,hP.2⟩
        intro q hq
        exact mem_product.mpr ⟨mem_univ _,mem_erase.mpr ⟨hj q hq, mem_univ _⟩⟩
      have hb := (matching_le_worth a _ _ _ hm).trans (huv.2 univ (univ.erase j))
      have he := Finset.sum_erase_add (s := univ) (f := v) (mem_univ j)
      have hj0 := hn.2 j
      linarith
