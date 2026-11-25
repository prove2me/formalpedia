-- Prove2me | solution 1 for Arxiv1605_04704.case_b2_rank_three
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T20:45:18.15511+00:00
-- url     : https://prove2.me/submissions/52282e97-7304-4a48-8a02-f8936605b2d2

import Mathlib
import Definitions.Def_Arxiv1605_04704_Basic

open Matrix

open Arxiv1605_04704 in
theorem solution (Mexp : Matrix (Fin 4) (Fin 4) ℝ) (U : Matrix.unitaryGroup (Fin 4) ℂ) (lam : Fin 4 → ℝ)
    (hdat : IsCovFilterData Mexp U lam) (hlam0 : 0 < lam 0)
    (hr : (covH U lam).rank = 3) :
    filt3 U lam = covMueller U lam := by
  classical
  have hanti : Antitone (covEig lam) := fun i j hij => max_le_max (hdat.1 hij) le_rfl
  have hnn : ∀ i, 0 ≤ covEig lam i := fun i => le_max_right _ _
  have hU1 : (U : Matrix (Fin 4) (Fin 4) ℂ) * star (U : Matrix (Fin 4) (Fin 4) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.1 U.2
  have hU2 : star (U : Matrix (Fin 4) (Fin 4) ℂ) * (U : Matrix (Fin 4) (Fin 4) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 U.2
  have hdU : IsUnit (U : Matrix (Fin 4) (Fin 4) ℂ).det := Matrix.isUnit_det_of_left_inverse hU2
  have hdUs : IsUnit (star (U : Matrix (Fin 4) (Fin 4) ℂ)).det :=
    Matrix.isUnit_det_of_left_inverse hU1
  have hrank : (covH U lam).rank =
      (Finset.univ.filter fun i => (covEig lam i : ℂ) ≠ 0).card := by
    unfold covH
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdUs, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdU,
      Matrix.rank_diagonal, Fintype.card_subtype]
  have h0pos : 0 < covEig lam 0 := lt_max_of_lt_left hlam0
  set S := ∑ j, covEig lam j with hS
  have hSpos : 0 < S := by
    rw [hS, Fin.sum_univ_four]; linarith [hnn 1, hnn 2, hnn 3]
  have hl : ∀ i, covLhat lam i = covEig lam i / S := fun i => rfl
  have hsum1 : covLhat lam 0 + covLhat lam 1 + covLhat lam 2 + covLhat lam 3 = 1 := by
    simp only [hl, ← add_div]
    rw [div_eq_one_iff_eq hSpos.ne', hS, Fin.sum_univ_four]
  have h3z : covEig lam 3 = 0 := by
    by_contra h3
    have h3' : (covEig lam 3 : ℂ) ≠ 0 := by exact_mod_cast h3
    have hpos3 : 0 < covEig lam 3 := lt_of_le_of_ne (hnn 3) (Ne.symm h3)
    have hall : ∀ i, (covEig lam i : ℂ) ≠ 0 := by
      intro i
      have : covEig lam 3 ≤ covEig lam i := hanti (Fin.le_last i)
      exact_mod_cast (by linarith : (0:ℝ) < covEig lam i).ne'
    have : (Finset.univ.filter fun i => (covEig lam i : ℂ) ≠ 0).card = 4 := by
      rw [Finset.filter_true_of_mem (fun i _ => hall i)]; rfl
    omega
  have hP : ipp3 (covLhat lam) = 1 := by
    unfold ipp3
    have : covLhat lam 3 = 0 := by rw [hl, h3z, zero_div]
    rw [this]; linarith
  unfold filt3
  rw [hP]; simp
