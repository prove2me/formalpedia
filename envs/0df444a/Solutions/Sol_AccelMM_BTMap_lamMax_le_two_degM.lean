-- Prove2me | solution 1 for AccelMM.BTMap.lamMax_le_two_degM
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T01:45:41.472469+00:00
-- url     : https://prove2.me/submissions/ee616e7d-9803-4645-8c63-20832029c66e

import Mathlib
import Definitions.Def_AccelMM_BTMap_Framework
import Definitions.Def_AccelMM_BTMap_Model

namespace Aux_AccelMM_Gersh

open AccelMM.BTMap Matrix

lemma mM_symm {n : ℕ} (d : Fin n → Fin n → ℕ) (i j : Fin n) : mM d i j = mM d j i := by
  unfold mM
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h), add_comm]

lemma mM_nonneg {n : ℕ} (d : Fin n → Fin n → ℕ) (i j : Fin n) : 0 ≤ mM d i j := by
  unfold mM; split_ifs <;> positivity

lemma lap_two {n : ℕ} (d : Fin n → Fin n → ℕ) (v : Fin n → ℝ) :
    2 * (v ⬝ᵥ (lapM d *ᵥ v)) = ∑ i, ∑ j, mM d i j * (v i - v j) ^ 2 := by
  have e1 : v ⬝ᵥ (lapM d *ᵥ v) =
      ∑ i, ∑ j, mM d i j * v i ^ 2 - ∑ i, ∑ j, mM d i j * v i * v j := by
    have hrow : ∀ i, ∑ j, lapM d i j * v j = (∑ j, mM d i j) * v i - ∑ j, mM d i j * v j := by
      intro i
      simp [lapM, Matrix.sub_apply, Matrix.diagonal_apply, sub_mul, Finset.sum_sub_distrib,
        ite_mul]
    simp only [dotProduct, Matrix.mulVec, hrow]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [mul_sub, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  have e2 : ∑ i, ∑ j, mM d i j * v j ^ 2 = ∑ i, ∑ j, mM d i j * v i ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [mM_symm]
  have e3 : 2 * (v ⬝ᵥ (lapM d *ᵥ v)) = ∑ i, ∑ j, mM d i j * (v i - v j) ^ 2 := by
    rw [e1]
    have : ∑ i, ∑ j, mM d i j * (v i - v j) ^ 2 = ∑ i, ∑ j, mM d i j * v i ^ 2
        - 2 * ∑ i, ∑ j, mM d i j * v i * v j + ∑ i, ∑ j, mM d i j * v j ^ 2 := by
      rw [Finset.mul_sum]
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _; ring
    rw [this, e2]; ring
  exact e3



lemma degM_ge {n : ℕ} (d : Fin n → Fin n → ℕ) (i : Fin n) : ∑ j, mM d i j ≤ degM d := by
  unfold degM
  exact le_ciSup (f := fun i => ∑ j, mM d i j) (Set.finite_range _).bddAbove i

lemma degM_nonneg {n : ℕ} (d : Fin n → Fin n → ℕ) : 0 ≤ degM d := by
  unfold degM
  exact Real.iSup_nonneg fun i => Finset.sum_nonneg fun j _ => mM_nonneg d i j

lemma quad_upper {n : ℕ} (d : Fin n → Fin n → ℕ) (v : Fin n → ℝ) :
    v ⬝ᵥ (lapM d *ᵥ v) ≤ 2 * degM d * ∑ i, v i ^ 2 := by
  have h2 := lap_two d v
  have h3 : ∑ i, ∑ j, mM d i j * (v i - v j) ^ 2 ≤
      ∑ i, ∑ j, (2 * (mM d i j * v i ^ 2) + 2 * (mM d i j * v j ^ 2)) := by
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    have := mM_nonneg d i j
    nlinarith [sq_nonneg (v i + v j), mul_nonneg this (sq_nonneg (v i + v j))]
  have h4 : ∑ i, ∑ j, mM d i j * v j ^ 2 = ∑ i, ∑ j, mM d i j * v i ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [mM_symm]
  have h5 : ∑ i, ∑ j, (2 * (mM d i j * v i ^ 2) + 2 * (mM d i j * v j ^ 2)) =
      4 * ∑ i, v i ^ 2 * ∑ j, mM d i j := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [h4]
    have : ∑ i, ∑ j, mM d i j * v i ^ 2 = ∑ i, v i ^ 2 * ∑ j, mM d i j := by
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    rw [this]; ring
  have h6 : ∑ i, v i ^ 2 * ∑ j, mM d i j ≤ degM d * ∑ i, v i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro i _
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (degM_ge d i) (sq_nonneg _)
  linarith

end Aux_AccelMM_Gersh

open AccelMM.BTMap Aux_AccelMM_Gersh in
theorem solution {n : ℕ} (d : Fin n → Fin n → ℕ) : lamMax d ≤ 2 * degM d := by
  unfold lamMax
  split_ifs with h
  · set hA := lapM_isHermitian d
    set k : Fin (Fintype.card (Fin n)) := ⟨0, by omega⟩
    set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))
    have h1 : hA.eigenvalues₀ k = hA.eigenvalues (e k) := by
      simp [Matrix.IsHermitian.eigenvalues, e]
    rw [h1, hA.eigenvalues_eq]
    have hq := quad_upper d ⇑(hA.eigenvectorBasis (e k))
    have hn : ∑ i, (hA.eigenvectorBasis (e k)) i ^ 2 = 1 := by
      have := EuclideanSpace.real_norm_sq_eq (hA.eigenvectorBasis (e k))
      rw [(hA.eigenvectorBasis).orthonormal.1 (e k)] at this
      simpa using this.symm
    rw [hn, mul_one] at hq
    simpa using hq
  · have := degM_nonneg d; linarith
