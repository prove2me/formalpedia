-- Prove2me | solution 1 for AssignmentGame.CoreCorners.worth_le_permutation_bound
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T21:12:09.886974+00:00
-- url     : https://prove2.me/submissions/b07b9a50-e558-4670-8b1b-f95dc948bcdb

import Theorems.Thm_AssignmentGame_CoreCorners_matching_extends_to_equiv

open AssignmentGame.CoreCorners

theorem solution {M N : Type*} [Fintype M] [Fintype N]
    [DecidableEq M] [DecidableEq N]
    (a : M → N → ℝ) (ha : ∀ i j, 0 ≤ a i j)
    (e : M ≃ N) (K : ℝ)
    (hK : ∀ f : M ≃ N, (∑ i, a i (f i)) ≤ K) :
    worth a Finset.univ Finset.univ ≤ K := by
  classical
  unfold worth
  apply Finset.sup'_le
  intro P hP
  have hmatch : IsMatching Finset.univ Finset.univ P := by
    exact (Finset.mem_filter.mp hP).2
  obtain ⟨f, hf⟩ := matching_extends_to_equiv e P hmatch
  have hsum : (∑ p ∈ P, a p.1 p.2) =
      ∑ i ∈ P.image Prod.fst, a i (f i) := by
    calc
      _ = ∑ p ∈ P, a p.1 (f p.1) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [hf p hp]
      _ = _ := by
        rw [Finset.sum_image]
        intro p hp q hq hfst
        exact hmatch.2.1 p hp q hq hfst
  rw [hsum]
  have hsub : P.image Prod.fst ⊆ (Finset.univ : Finset M) := by simp
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (by intro i _ _; exact ha i (f i))).trans (hK f)
