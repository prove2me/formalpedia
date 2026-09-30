-- Prove2me | solution 1 for AssignmentGame.CoreCorners.core_lattice
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:09:47.320842+00:00
-- url     : https://prove2.me/submissions/89f14c77-2fe5-4f8b-aacc-834639acedd9

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


private theorem matching_le_payoffs {M N : Type*} [Fintype M] [Fintype N]
    (a : M → N → ℝ) (u : M → ℝ) (v : N → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ j, 0 ≤ v j) (hp : ∀ i j, a i j ≤ u i+v j)
    (A : Finset M) (B : Finset N) (P : Finset (M × N)) (hP : IsMatching A B P) :
    ∑ p ∈ P, a p.1 p.2 ≤ ∑ i ∈ A, u i + ∑ j ∈ B, v j := by
  classical
  have hsu : ∑ i ∈ P.image Prod.fst, u i = ∑ p ∈ P, u p.1 := Finset.sum_image hP.2.1
  have hsv : ∑ j ∈ P.image Prod.snd, v j = ∑ p ∈ P, v p.2 := Finset.sum_image hP.2.2
  have hAu : P.image Prod.fst ⊆ A := by
    intro i hi
    obtain ⟨p,hpP,rfl⟩ := mem_image.mp hi
    exact (mem_product.mp (hP.1 hpP)).1
  have hBv : P.image Prod.snd ⊆ B := by
    intro i hi
    obtain ⟨p,hpP,rfl⟩ := mem_image.mp hi
    exact (mem_product.mp (hP.1 hpP)).2
  have hbu : ∑ p ∈ P, u p.1 ≤ ∑ i ∈ A, u i := by
    rw [← hsu]
    exact sum_le_sum_of_subset_of_nonneg hAu (fun i _ _ => hu i)
  have hbv : ∑ p ∈ P, v p.2 ≤ ∑ j ∈ B, v j := by
    rw [← hsv]
    exact sum_le_sum_of_subset_of_nonneg hBv (fun j _ _ => hv j)
  have hb : ∑ p ∈ P, a p.1 p.2 ≤ ∑ p ∈ P, (u p.1+v p.2) := sum_le_sum (fun p _ => hp p.1 p.2)
  rw [sum_add_distrib] at hb
  linarith

private theorem worth_le_payoffs {M N : Type*} [Fintype M] [Fintype N]
    (a : M → N → ℝ) (u : M → ℝ) (v : N → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ j, 0 ≤ v j) (hp : ∀ i j, a i j ≤ u i+v j)
    (A : Finset M) (B : Finset N) : worth a A B ≤ ∑ i ∈ A, u i + ∑ j ∈ B, v j := by
  classical
  unfold worth
  apply Finset.sup'_le
  intro P hP
  exact matching_le_payoffs a u v hu hv hp A B P (mem_filter.mp hP).2

theorem solution {M N : Type*} [Fintype M] [Fintype N]
    (a : M → N → ℝ) (ha : ∀ i j, 0 ≤ a i j)
    (u' u'' : M → ℝ) (v' v'' : N → ℝ)
    (h' : (u', v') ∈ core a) (h'' : (u'', v'') ∈ core a) :
    ((fun i => min (u' i) (u'' i)), (fun j => max (v' j) (v'' j))) ∈ core a ∧
    ((fun i => max (u' i) (u'' i)), (fun j => min (v' j) (v'' j))) ∈ core a := by
  have hn' := core_nonneg a (u',v') h'
  have hn'' := core_nonneg a (u'',v'') h''
  have hulo (i : M) : 0 ≤ min (u' i) (u'' i) := le_min (hn'.1 i) (hn''.1 i)
  have huhi (i : M) : 0 ≤ max (u' i) (u'' i) := (hn'.1 i).trans (le_max_left _ _)
  have hvlo (j : N) : 0 ≤ min (v' j) (v'' j) := le_min (hn'.2 j) (hn''.2 j)
  have hvhi (j : N) : 0 ≤ max (v' j) (v'' j) := (hn'.2 j).trans (le_max_left _ _)
  have hp1 (i : M) (j : N) : a i j ≤ min (u' i) (u'' i) + max (v' j) (v'' j) := by
    rcases le_total (u' i) (u'' i) with h | h
    · rw [min_eq_left h]
      exact (pair_lower a u' v' h' i j).trans (add_le_add le_rfl (le_max_left _ _))
    · rw [min_eq_right h]
      exact (pair_lower a u'' v'' h'' i j).trans (add_le_add le_rfl (le_max_right _ _))
  have hp2 (i : M) (j : N) : a i j ≤ max (u' i) (u'' i) + min (v' j) (v'' j) := by
    rcases le_total (v' j) (v'' j) with h | h
    · rw [min_eq_left h]
      exact (pair_lower a u' v' h' i j).trans (add_le_add (le_max_left _ _) le_rfl)
    · rw [min_eq_right h]
      exact (pair_lower a u'' v'' h'' i j).trans (add_le_add (le_max_right _ _) le_rfl)
  have h1 := worth_le_payoffs a _ _ hulo hvhi hp1 univ univ
  have h2 := worth_le_payoffs a _ _ huhi hvlo hp2 univ univ
  have hsu : (∑ i, min (u' i) (u'' i)) + (∑ i, max (u' i) (u'' i)) = (∑ i, u' i)+(∑ i, u'' i) := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    exact min_add_max _ _
  have hsv : (∑ j, max (v' j) (v'' j)) + (∑ j, min (v' j) (v'' j)) = (∑ j, v' j)+(∑ j, v'' j) := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    exact max_add_min _ _
  constructor
  · refine ⟨?_, fun A B => worth_le_payoffs a _ _ hulo hvhi hp1 A B⟩
    linarith [h'.1,h''.1]
  · refine ⟨?_, fun A B => worth_le_payoffs a _ _ huhi hvlo hp2 A B⟩
    linarith [h'.1,h''.1]
