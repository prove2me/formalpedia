-- Prove2me | solution 1 for Arxiv1605_04704.case_c1_not_proportional
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T20:44:02.725494+00:00
-- url     : https://prove2.me/submissions/b4296f2d-d89c-4356-9de6-c44fffdfccc0

import Mathlib
import Definitions.Def_Arxiv1605_04704_Basic

open Matrix

open Arxiv1605_04704 in
theorem solution (Mexp : Matrix (Fin 4) (Fin 4) ℝ) (U : Matrix.unitaryGroup (Fin 4) ℂ) (lam : Fin 4 → ℝ)
    (hdat : IsCovFilterData Mexp U lam) (hlam0 : 0 < lam 0)
    (hr : 2 < (covH U lam).rank) :
    let l := covLhat lam
    l 0 ≠ l 1 →
      ∀ k : ℝ, ¬ ((l 0 - l 2) / (l 0 + l 1 - 2 * l 2) = k * l 0 ∧
        (l 1 - l 2) / (l 0 + l 1 - 2 * l 2) = k * l 1) := by
  classical
  intro l hne k ⟨h1, h2⟩
  have hanti : Antitone (covEig lam) := fun i j hij => max_le_max (hdat.1 hij) le_rfl
  have hnn : ∀ i, 0 ≤ covEig lam i := fun i => le_max_right _ _
  have hU1 : (U : Matrix (Fin 4) (Fin 4) ℂ) * star (U : Matrix (Fin 4) (Fin 4) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.1 U.2
  have hU2 : star (U : Matrix (Fin 4) (Fin 4) ℂ) * (U : Matrix (Fin 4) (Fin 4) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 U.2
  have hdU : IsUnit (U : Matrix (Fin 4) (Fin 4) ℂ).det := Matrix.isUnit_det_of_left_inverse hU2
  have hdUs : IsUnit (star (U : Matrix (Fin 4) (Fin 4) ℂ)).det :=
    Matrix.isUnit_det_of_left_inverse hU1
  have hrank : (covH U lam).rank = Fintype.card {i // (covEig lam i : ℂ) ≠ 0} := by
    unfold covH
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdUs, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdU,
      Matrix.rank_diagonal]
  have h2pos : 0 < covEig lam 2 := by
    by_contra hc
    have h2z : covEig lam 2 = 0 := le_antisymm (not_lt.1 hc) (hnn 2)
    have h3z : covEig lam 3 = 0 :=
      le_antisymm (h2z ▸ hanti (by decide : (2 : Fin 4) ≤ 3)) (hnn 3)
    have : Fintype.card {i // (covEig lam i : ℂ) ≠ 0} ≤ 2 := by
      rw [Fintype.card_subtype]
      calc (Finset.univ.filter fun i => (covEig lam i : ℂ) ≠ 0).card ≤ ({0, 1} : Finset (Fin 4)).card := by
            apply Finset.card_le_card
            intro i hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
            fin_cases i <;> simp_all
        _ = 2 := by decide
    omega
  have h0pos : 0 < covEig lam 0 := lt_max_of_lt_left hlam0
  set S := ∑ j, covEig lam j with hS
  have hSpos : 0 < S := by
    rw [hS, Fin.sum_univ_four]; linarith [hnn 1, hnn 2, hnn 3]
  have hl : ∀ i, l i = covEig lam i / S := fun i => rfl
  have e01 : covEig lam 1 ≤ covEig lam 0 := hanti (by decide)
  have e12 : covEig lam 2 ≤ covEig lam 1 := hanti (by decide)
  have hne' : covEig lam 0 ≠ covEig lam 1 := by
    intro h; apply hne; rw [hl, hl, h]
  have hD : 0 < l 0 + l 1 - 2 * l 2 := by
    rw [hl, hl, hl, ← add_div, ← mul_div_assoc, ← sub_div]
    apply div_pos _ hSpos
    have := lt_of_le_of_ne e01 (Ne.symm hne')
    linarith
  rw [div_eq_iff hD.ne'] at h1 h2
  have key : l 2 * (l 0 - l 1) = 0 := by linear_combination l 1 * h1 - l 0 * h2
  have hl2 : 0 < l 2 := by rw [hl]; exact div_pos h2pos hSpos
  have hl01 : l 0 - l 1 ≠ 0 := sub_ne_zero.2 hne
  exact (mul_ne_zero hl2.ne' hl01) key
