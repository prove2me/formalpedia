-- Prove2me | solution 1 for Arxiv1605_04704.case_b1_not_proportional
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T20:46:28.487887+00:00
-- url     : https://prove2.me/submissions/e70e159d-3789-409d-8e29-0de5143ae632

import Mathlib
import Definitions.Def_Arxiv1605_04704_Basic

open Matrix

open Arxiv1605_04704 in
theorem solution (Mexp : Matrix (Fin 4) (Fin 4) ℝ) (U : Matrix.unitaryGroup (Fin 4) ℂ) (lam : Fin 4 → ℝ)
    (hdat : IsCovFilterData Mexp U lam) (hlam0 : 0 < lam 0)
    (hr : (covH U lam).rank = 4) :
    let l := covLhat lam
    ¬ (l 0 = l 1 ∧ l 1 = l 2) →
      ∀ k : ℝ, ¬ ((l 0 - l 3) / (1 - 4 * l 3) = k * l 0 ∧ (l 1 - l 3) / (1 - 4 * l 3) = k * l 1 ∧
        (l 2 - l 3) / (1 - 4 * l 3) = k * l 2) := by
  intro l hne k ⟨h0, h1, h2⟩
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
  have h3pos : 0 < covEig lam 3 := by
    by_contra h3
    have h3z : covEig lam 3 = 0 := le_antisymm (not_lt.1 h3) (hnn 3)
    have : (Finset.univ.filter fun i => (covEig lam i : ℂ) ≠ 0).card ≤ 3 := by
      calc _ ≤ ({0, 1, 2} : Finset (Fin 4)).card := by
            apply Finset.card_le_card
            intro i hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
            fin_cases i <;> simp_all
        _ = 3 := by decide
    omega
  have e01 : covEig lam 1 ≤ covEig lam 0 := hanti (by decide)
  have e12 : covEig lam 2 ≤ covEig lam 1 := hanti (by decide)
  have e23 : covEig lam 3 ≤ covEig lam 2 := hanti (by decide)
  have l01 : l 1 ≤ l 0 := div_le_div_of_nonneg_right e01 hSpos.le
  have l12 : l 2 ≤ l 1 := div_le_div_of_nonneg_right e12 hSpos.le
  have l23 : l 3 ≤ l 2 := div_le_div_of_nonneg_right e23 hSpos.le
  have l3pos : 0 < l 3 := div_pos h3pos hSpos
  have hsum : l 0 + l 1 + l 2 + l 3 = 1 := hsum1
  by_cases hD : 1 - 4 * l 3 = 0
  · apply hne
    constructor <;> linarith
  rw [div_eq_iff hD] at h0 h1 h2
  have k01 : l 3 * (l 0 - l 1) = 0 := by linear_combination l 1 * h0 - l 0 * h1
  have k12 : l 3 * (l 1 - l 2) = 0 := by linear_combination l 2 * h1 - l 1 * h2
  apply hne
  constructor
  · have := (mul_eq_zero.1 k01).resolve_left l3pos.ne'; linarith
  · have := (mul_eq_zero.1 k12).resolve_left l3pos.ne'; linarith
