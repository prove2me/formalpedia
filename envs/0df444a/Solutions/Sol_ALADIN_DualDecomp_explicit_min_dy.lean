-- Prove2me | solution 1 for ALADIN.DualDecomp.explicit_min_dy
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:57:13.214554+00:00
-- url     : https://prove2.me/submissions/6d898f72-e1c3-42b6-b0cc-8e10d4ca85b4

import Mathlib

open Matrix

private theorem reduced_props {n nh : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin nh) (Fin n) ℝ) (hH : H.PosDef) (hC : C.rank = nh) :
    let Q := C * H⁻¹ * Cᵀ
    let P := H⁻¹ - H⁻¹ * Cᵀ * Q⁻¹ * C * H⁻¹
    Q.PosDef ∧ P.IsHermitian ∧ C * P = 0 ∧ P * Cᵀ = 0 ∧
      H * P = 1 - Cᵀ * Q⁻¹ * C * H⁻¹ ∧
      P * H = 1 - H⁻¹ * Cᵀ * Q⁻¹ * C ∧ P.PosSemidef := by
  dsimp only
  let Q := C * H⁻¹ * Cᵀ
  let P := H⁻¹ - H⁻¹ * Cᵀ * Q⁻¹ * C * H⁻¹
  have hinj : Function.Injective C.vecMul := by
    rw [Matrix.vecMul_injective_iff, linearIndependent_iff_card_eq_finrank_span]
    simpa [← C.rank_eq_finrank_span_row, Set.finrank] using hC.symm
  have hQ : Q.PosDef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hH.inv.mul_mul_conjTranspose_same hinj
  have hHunit : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  have hQunit : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ.isUnit
  have hHsym : H⁻¹ᵀ = H⁻¹ := by simpa using hH.inv.isHermitian.eq
  have hQsym : Q⁻¹ᵀ = Q⁻¹ := by simpa using hQ.inv.isHermitian.eq
  have hPsym : Pᵀ = P := by
    dsimp [P]
    simp only [transpose_sub, transpose_mul, transpose_transpose, hHsym, hQsym]
    simp only [Matrix.mul_assoc]
  have hCP : C * P = 0 := by
    dsimp [P]
    rw [Matrix.mul_sub]
    have he : C * (H⁻¹ * Cᵀ * Q⁻¹ * C * H⁻¹) = Q * Q⁻¹ * (C * H⁻¹) := by
      dsimp [Q]
      simp only [Matrix.mul_assoc]
    rw [he, Q.mul_nonsing_inv hQunit, Matrix.one_mul, sub_self]
  have hPC : P * Cᵀ = 0 := by
    have := congrArg Matrix.transpose hCP
    simpa only [transpose_mul, hPsym, transpose_zero] using this
  have hHP : H * P = 1 - Cᵀ * Q⁻¹ * C * H⁻¹ := by
    dsimp [P]
    rw [Matrix.mul_sub, H.mul_nonsing_inv hHunit]
    have he : H * (H⁻¹ * Cᵀ * Q⁻¹ * C * H⁻¹) =
        (H * H⁻¹) * (Cᵀ * Q⁻¹ * C * H⁻¹) := by simp only [Matrix.mul_assoc]
    rw [he, H.mul_nonsing_inv hHunit, Matrix.one_mul]
  have hPH : P * H = 1 - H⁻¹ * Cᵀ * Q⁻¹ * C := by
    have := congrArg Matrix.transpose hHP
    simpa only [transpose_mul, transpose_sub, transpose_one, transpose_transpose,
      hPsym, hHsym, hQsym, show Hᵀ = H by simpa using hH.isHermitian.eq,
      Matrix.mul_assoc] using this
  have hPHP : P * H * P = P := by
    rw [hPH, Matrix.sub_mul, Matrix.one_mul]
    have he : H⁻¹ * Cᵀ * Q⁻¹ * C * P = H⁻¹ * Cᵀ * Q⁻¹ * (C * P) := by
      simp only [Matrix.mul_assoc]
    rw [he, hCP, Matrix.mul_zero, sub_zero]
  have hP : P.PosSemidef := by
    have hp := hH.posSemidef.conjTranspose_mul_mul_same P
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hPsym, hPHP] using hp
  exact ⟨hQ, by simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hPsym,
    hCP, hPC, hHP, hPH, hP⟩

theorem solution {n nh : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin nh) (Fin n) ℝ)
    (hH : H.PosDef) (hC : C.rank = nh) (w : Fin n → ℝ) :
    let P := H⁻¹ - H⁻¹ * Cᵀ * (C * H⁻¹ * Cᵀ)⁻¹ * C * H⁻¹
    IsUnit (C * H⁻¹ * Cᵀ).det ∧
    C *ᵥ (-(P *ᵥ w)) = 0 ∧
    IsMinOn (fun Δ : Fin n → ℝ => 1 / 2 * (Δ ⬝ᵥ (H *ᵥ Δ)) + w ⬝ᵥ Δ) {Δ | C *ᵥ Δ = 0}
      (-(P *ᵥ w)) ∧
    1 / 2 * ((-(P *ᵥ w)) ⬝ᵥ (H *ᵥ (-(P *ᵥ w)))) + w ⬝ᵥ (-(P *ᵥ w)) = -(1 / 2) * (w ⬝ᵥ (P *ᵥ w)) ∧
    0 ≤ w ⬝ᵥ (P *ᵥ w) := by
  let Q := C * H⁻¹ * Cᵀ
  let P := H⁻¹ - H⁻¹ * Cᵀ * Q⁻¹ * C * H⁻¹
  change IsUnit Q.det ∧ C *ᵥ (-(P *ᵥ w)) = 0 ∧
    IsMinOn (fun Δ : Fin n → ℝ => 1 / 2 * (Δ ⬝ᵥ (H *ᵥ Δ)) + w ⬝ᵥ Δ)
      {Δ | C *ᵥ Δ = 0} (-(P *ᵥ w)) ∧
    1 / 2 * ((-(P *ᵥ w)) ⬝ᵥ (H *ᵥ (-(P *ᵥ w)))) + w ⬝ᵥ (-(P *ᵥ w)) =
      -(1 / 2) * (w ⬝ᵥ (P *ᵥ w)) ∧ 0 ≤ w ⬝ᵥ (P *ᵥ w)
  obtain ⟨hQ, hPsym, hCP, hPC, hHP, hPH, hP⟩ := reduced_props H C hH hC
  change Q.PosDef at hQ
  change C * P = 0 at hCP
  change H * P = 1 - Cᵀ * Q⁻¹ * C * H⁻¹ at hHP
  have hCq : C *ᵥ (P *ᵥ w) = 0 := by
    rw [Matrix.mulVec_mulVec, hCP, Matrix.zero_mulVec]
  have horth (v : Fin n → ℝ) (hv : C *ᵥ v = 0) :
      v ⬝ᵥ (H *ᵥ (P *ᵥ w)) = v ⬝ᵥ w := by
    rw [Matrix.mulVec_mulVec, hHP, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
    have hz : v ⬝ᵥ ((Cᵀ * Q⁻¹ * C * H⁻¹) *ᵥ w) = 0 := by
      simp only [← Matrix.mulVec_mulVec]
      rw [dotProduct_mulVec, vecMul_transpose, hv, zero_dotProduct]
    rw [hz, sub_zero]
  have hsym (u v : Fin n → ℝ) : u ⬝ᵥ (H *ᵥ v) = v ⬝ᵥ (H *ᵥ u) := by
    rw [dotProduct_mulVec, ← mulVec_transpose,
      show Hᵀ = H by simpa using hH.isHermitian.eq, dotProduct_comm]
  have hvalue : 1 / 2 * ((-(P *ᵥ w)) ⬝ᵥ (H *ᵥ (-(P *ᵥ w)))) +
      w ⬝ᵥ (-(P *ᵥ w)) = -(1 / 2) * (w ⬝ᵥ (P *ᵥ w)) := by
    simp only [Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
    rw [horth _ hCq, dotProduct_comm (P *ᵥ w) w]
    ring
  refine ⟨(Matrix.isUnit_iff_isUnit_det Q).mp hQ.isUnit, ?_, ?_, hvalue, ?_⟩
  · simpa [Matrix.mulVec_neg] using hCq
  · intro v hv
    change C *ᵥ v = 0 at hv
    change 1 / 2 * ((-(P *ᵥ w)) ⬝ᵥ (H *ᵥ (-(P *ᵥ w)))) + w ⬝ᵥ (-(P *ᵥ w)) ≤ _
    rw [hvalue]
    have hn := hH.posSemidef.dotProduct_mulVec_nonneg (v + P *ᵥ w)
    simp only [star_trivial, Matrix.mulVec_add, add_dotProduct, dotProduct_add] at hn
    rw [horth v hv, horth _ hCq, hsym (P *ᵥ w) v, horth v hv,
      dotProduct_comm v w, dotProduct_comm (P *ᵥ w) w] at hn
    linarith
  · simpa only [star_trivial] using hP.dotProduct_mulVec_nonneg w
