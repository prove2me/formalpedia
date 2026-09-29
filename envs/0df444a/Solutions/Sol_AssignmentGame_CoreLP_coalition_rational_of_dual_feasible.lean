-- Prove2me | solution 1 for AssignmentGame.CoreLP.coalition_rational_of_dual_feasible
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T00:17:26.899804+00:00
-- url     : https://prove2.me/submissions/21267b29-5c13-4789-a0c0-a77214721168

import Mathlib
import Definitions.Def_AssignmentGame_CoreLP_Game

open AssignmentGame.CoreLP
open Finset

theorem solution {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ)
    (ha : ∀ i j, 0 ≤ a i j) (p : (M → ℝ) × (N → ℝ)) (hp : DualFeasible a p)
    (A : Finset M) (B : Finset N) :
    worth a A B ≤ ∑ i ∈ A, p.1 i + ∑ j ∈ B, p.2 j := by
  classical
  obtain ⟨hu, hv, hab⟩ := hp
  unfold worth
  refine Finset.sup'_le _ _ ?_
  intro P hP
  have hPm : IsMatching A B P := by
    unfold matchings at hP
    exact (Finset.mem_filter.mp hP).2
  obtain ⟨hsub, hinj1, hinj2⟩ := hPm
  have h1 : ∑ q ∈ P, a q.1 q.2 ≤ ∑ q ∈ P, (p.1 q.1 + p.2 q.2) :=
    Finset.sum_le_sum fun q _ => hab q.1 q.2
  have h2 : ∑ q ∈ P, (p.1 q.1 + p.2 q.2) = (∑ q ∈ P, p.1 q.1) + ∑ q ∈ P, p.2 q.2 :=
    Finset.sum_add_distrib
  have h3 : ∑ i ∈ P.image Prod.fst, p.1 i = ∑ q ∈ P, p.1 q.1 :=
    Finset.sum_image (fun x hx y hy hxy => hinj1 x hx y hy hxy)
  have h4 : ∑ j ∈ P.image Prod.snd, p.2 j = ∑ q ∈ P, p.2 q.2 :=
    Finset.sum_image (fun x hx y hy hxy => hinj2 x hx y hy hxy)
  have h5 : P.image Prod.fst ⊆ A := by
    intro i hi
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_product.mp (hsub hq)).1
  have h6 : P.image Prod.snd ⊆ B := by
    intro j hj
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
    exact (Finset.mem_product.mp (hsub hq)).2
  have h7 : ∑ i ∈ P.image Prod.fst, p.1 i ≤ ∑ i ∈ A, p.1 i :=
    Finset.sum_le_sum_of_subset_of_nonneg h5 (fun i _ _ => hu i)
  have h8 : ∑ j ∈ P.image Prod.snd, p.2 j ≤ ∑ j ∈ B, p.2 j :=
    Finset.sum_le_sum_of_subset_of_nonneg h6 (fun j _ _ => hv j)
  linarith
