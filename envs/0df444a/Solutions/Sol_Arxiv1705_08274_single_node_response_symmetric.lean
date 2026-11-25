-- Prove2me | solution 1 for Arxiv1705_08274.single_node_response_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T20:26:22.879377+00:00
-- url     : https://prove2.me/submissions/d149a4ce-427d-4b48-814f-caa73c4ffacf

import Mathlib
import Definitions.Def_Arxiv1705_08274_Basic

open Matrix
open Arxiv1705_08274

section
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma nr_blocks (e11 e12 e21 e22 : Matrix n n ℝ) (hE : IsUnit e22.det)
    (h21 : e21 * e22 + e22 * e12 = 0) (h22 : e21 * e21 + e22 * e11 = 1) :
    e22⁻¹ = e11 - e12 * e22⁻¹ * e21 ∧ -(e22⁻¹ * e21) = e12 * e22⁻¹ := by
  set i := e22⁻¹ with hi
  have hi1 : i * e22 = 1 := Matrix.nonsing_inv_mul _ hE
  have hi2 : e22 * i = 1 := Matrix.mul_nonsing_inv _ hE
  have k1 : e22 * e12 = -(e21 * e22) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact h21
  have he12 : e12 = -(i * e21 * e22) := by
    calc e12 = (i * e22) * e12 := by rw [hi1, Matrix.one_mul]
      _ = i * (e22 * e12) := by rw [Matrix.mul_assoc]
      _ = -(i * e21 * e22) := by rw [k1]; noncomm_ring
  constructor
  · calc i = i * (e21 * e21 + e22 * e11) := by rw [h22, Matrix.mul_one]
      _ = i * e21 * e21 + (i * e22) * e11 := by noncomm_ring
      _ = i * e21 * e21 + e11 := by rw [hi1, Matrix.one_mul]
      _ = e11 - e12 * i * e21 := by
        have : (-(i * e21 * e22)) * i * e21 = -(i * e21 * (e22 * i) * e21) := by noncomm_ring
        rw [he12, this, hi2, Matrix.mul_one]; abel
  · have : (-(i * e21 * e22)) * i = -(i * e21 * (e22 * i)) := by noncomm_ring
    rw [he12, this, hi2, Matrix.mul_one]

lemma nr_resp (E : Matrix (n ⊕ n) (n ⊕ n) ℝ) (hE : IsUnit E.toBlocks₂₂.det) :
    respOfProp E = fromBlocks E.toBlocks₂₂⁻¹ (-(E.toBlocks₂₂⁻¹ * E.toBlocks₂₁))
      (E.toBlocks₁₂ * E.toBlocks₂₂⁻¹)
      (E.toBlocks₁₁ - E.toBlocks₁₂ * E.toBlocks₂₂⁻¹ * E.toBlocks₂₁) := by
  have hi1 : E.toBlocks₂₂⁻¹ * E.toBlocks₂₂ = 1 := Matrix.nonsing_inv_mul _ hE
  have hL : fromBlocks 0 E.toBlocks₂₂⁻¹ (-1) (E.toBlocks₁₂ * E.toBlocks₂₂⁻¹) *
      fromBlocks E.toBlocks₁₂ (-1) E.toBlocks₂₂ 0 = 1 := by
    rw [fromBlocks_multiply, ← fromBlocks_one]
    congr 1
    · simp [hi1]
    · simp
    · rw [Matrix.mul_assoc, hi1]; simp
    · simp
  unfold respOfProp
  rw [Matrix.inv_eq_left_inv hL, fromBlocks_multiply]
  congr 1
  · simp
  · simp
  · simp
  · simp [sub_eq_add_neg]

/-- swap matrix -/
def nrJ : Matrix (n ⊕ n) (n ⊕ n) ℝ := fromBlocks 0 1 1 0

lemma nrJ_sq : (nrJ : Matrix (n ⊕ n) (n ⊕ n) ℝ) * nrJ = 1 := by
  simp [nrJ, fromBlocks_multiply, fromBlocks_one]

lemma nr_conjA (a b : Matrix n n ℝ) (h : ℝ) :
    (nrJ : Matrix (n ⊕ n) (n ⊕ n) ℝ) * (-(h • fromBlocks a (-b) b (-a))) * nrJ =
      h • fromBlocks a (-b) b (-a) := by
  simp [nrJ, fromBlocks_multiply, fromBlocks_smul, fromBlocks_neg]

lemma nr_exp (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) (h : ℝ)
    (hA : (nrJ : Matrix (n ⊕ n) (n ⊕ n) ℝ) * (-(h • A)) * nrJ = h • A) :
    nodeExp A h * (nrJ * nodeExp A h * nrJ) = 1 := by
  have hJu : IsUnit (nrJ : Matrix (n ⊕ n) (n ⊕ n) ℝ) := by
    exact (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse nrJ_sq)
  have hJi : (nrJ : Matrix (n ⊕ n) (n ⊕ n) ℝ)⁻¹ = nrJ := Matrix.inv_eq_left_inv nrJ_sq
  have hc : nrJ * nodeExp A h * nrJ = NormedSpace.exp (h • A) := by
    unfold nodeExp
    have e : (nrJ : Matrix (n ⊕ n) (n ⊕ n) ℝ) * NormedSpace.exp (-(h • A)) * nrJ =
        nrJ * NormedSpace.exp (-(h • A)) * nrJ⁻¹ := by rw [hJi]
    rw [e, ← Matrix.exp_conj _ _ hJu, hJi, hA]
  rw [hc]
  unfold nodeExp
  rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl (h • A)).neg_left), neg_add_cancel,
    NormedSpace.exp_zero]
end

theorem solution {N : ℕ} (S : DOModel N) (hS : S.Admissible)
    (h : ℝ) (hh : 0 < h) (hE : IsUnit (nodeExp S.jacobian h).toBlocks₂₂.det) :
    let E := nodeExp S.jacobian h
    let R := respOfProp E
    R = fromBlocks E.toBlocks₂₂⁻¹ (-(E.toBlocks₂₂⁻¹ * E.toBlocks₂₁)) (E.toBlocks₁₂ * E.toBlocks₂₂⁻¹)
      (E.toBlocks₁₁ - E.toBlocks₁₂ * E.toBlocks₂₂⁻¹ * E.toBlocks₂₁) ∧
    IsSymmetricResponse R ∧
    E.toBlocks₂₂⁻¹ = E.toBlocks₁₁ - E.toBlocks₁₂ * E.toBlocks₂₂⁻¹ * E.toBlocks₂₁ ∧
    -(E.toBlocks₂₂⁻¹ * E.toBlocks₂₁) = E.toBlocks₁₂ * E.toBlocks₂₂⁻¹ := by
  intro E R
  have hEQ := nr_exp S.jacobian h (nr_conjA S.alpha S.beta h)
  have hEQ' : E * (nrJ * E * nrJ) = 1 := hEQ
  rw [← fromBlocks_toBlocks E] at hEQ'
  simp only [nrJ, fromBlocks_multiply] at hEQ'
  simp at hEQ'
  rw [← fromBlocks_one] at hEQ'
  have h21 := congrArg Matrix.toBlocks₂₁ hEQ'
  have h22 := congrArg Matrix.toBlocks₂₂ hEQ'
  simp only [toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂] at h21 h22
  obtain ⟨g3, g4⟩ := nr_blocks E.toBlocks₁₁ E.toBlocks₁₂ E.toBlocks₂₁ E.toBlocks₂₂ hE h21 h22
  have hR := nr_resp E hE
  refine ⟨hR, ?_, g3, g4⟩
  unfold IsSymmetricResponse
  rw [show R = respOfProp E from rfl, hR]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₂, toBlocks_fromBlocks₁₂,
    toBlocks_fromBlocks₂₁]
  exact ⟨g3, g4⟩

