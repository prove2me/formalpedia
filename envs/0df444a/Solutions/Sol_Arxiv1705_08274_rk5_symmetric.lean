-- Prove2me | solution 1 for Arxiv1705_08274.rk5_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T05:17:28.944807+00:00
-- url     : https://prove2.me/submissions/8cc6c09d-0ead-4d2d-bf5f-ca9530752e94

import Mathlib
import Definitions.Def_Arxiv1705_08274_Basic

open Matrix

namespace S70PS
open Arxiv1705_08274

variable {n : Type*} [Fintype n] [DecidableEq n]

def swp (n : Type*) [DecidableEq n] : Matrix (n ⊕ n) (n ⊕ n) ℝ := fromBlocks 0 1 1 0

lemma swp_sq : swp n * swp n = 1 := by
  rw [swp, fromBlocks_multiply]; simp [fromBlocks_one]

lemma swp_conj (E : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    swp n * E * swp n = fromBlocks E.toBlocks₂₂ E.toBlocks₂₁ E.toBlocks₁₂ E.toBlocks₁₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks E]
  rw [swp, fromBlocks_multiply, fromBlocks_multiply]
  simp

lemma swp_pow (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) (j : ℕ) :
    swp n * A ^ j * swp n = (swp n * A * swp n) ^ j := by
  induction j with
  | zero => simp [swp_sq]
  | succ j ih =>
    rw [pow_succ, pow_succ, ← ih]
    calc swp n * (A ^ j * A) * swp n = swp n * A ^ j * (swp n * swp n) * A * swp n := by
          rw [swp_sq]; simp [Matrix.mul_assoc]
      _ = _ := by simp [Matrix.mul_assoc]

lemma swp_inv : (swp n)⁻¹ = swp n := Matrix.inv_eq_left_inv swp_sq

/-- matrices anti-commuting with the swap give a symmetric response -/
lemma symm_of_anti (A B : Matrix (n ⊕ n) (n ⊕ n) ℝ) (hA : swp n * A * swp n = -A)
    (hB : swp n * B * swp n = -B) : IsSymmetricResponse (A⁻¹ * B) := by
  have hAi : swp n * A⁻¹ * swp n = -A⁻¹ := by
    have : (swp n * A * swp n)⁻¹ = swp n * A⁻¹ * swp n := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, swp_inv, Matrix.mul_assoc]
    have hneg : (-A)⁻¹ = -A⁻¹ := by
      rw [show -A = A * (-1) by simp, Matrix.mul_inv_rev,
        Matrix.inv_eq_left_inv (show (-1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) * (-1) = 1 by simp)]
      simp
    rw [← this, hA, hneg]
  have hR : swp n * (A⁻¹ * B) * swp n = A⁻¹ * B := by
    calc swp n * (A⁻¹ * B) * swp n = (swp n * A⁻¹ * swp n) * (swp n * B * swp n) := by
          simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (swp n) (swp n), swp_sq, Matrix.one_mul]
      _ = A⁻¹ * B := by rw [hAi, hB, neg_mul_neg]
  rw [swp_conj] at hR
  have h11 := congrArg Matrix.toBlocks₁₁ hR
  have h12 := congrArg Matrix.toBlocks₁₂ hR
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂] at h11 h12
  exact ⟨h11.symm, h12.symm⟩

lemma anti_form (X Y : Matrix n n ℝ) :
    swp n * fromBlocks X Y (-Y) (-X) * swp n = -fromBlocks X Y (-Y) (-X) := by
  rw [swp_conj]; simp [fromBlocks_neg]

lemma resp_form (Ps : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    IsSymmetricResponse
      ((fromBlocks (-Ps.toBlocks₂₁) Ps.toBlocks₁₁ (-Ps.toBlocks₁₁) Ps.toBlocks₂₁)⁻¹ *
        fromBlocks (-Ps.toBlocks₁₂) Ps.toBlocks₂₂ (-Ps.toBlocks₂₂) Ps.toBlocks₁₂) := by
  apply symm_of_anti
  · have := anti_form (-Ps.toBlocks₂₁) Ps.toBlocks₁₁; simpa using this
  · have := anti_form (-Ps.toBlocks₁₂) Ps.toBlocks₂₂; simpa using this


noncomputable def ee : ℕ → ℝ
  | 1 => 1 / 2
  | 2 => 1 / 8
  | 3 => 1 / 48
  | 4 => 1 / 384
  | 5 => 1 / 3840
  | 6 => 1 / 133120
  | _ => 0

lemma rk5_poly (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) (t : ℝ) :
    rk5Pstar A t = 1 + ∑ k ∈ Finset.Icc 1 6, (ee k * t ^ k) • A ^ k := by
  have hI : Finset.Icc 1 6 = {1, 2, 3, 4, 5, 6} := by decide
  rw [hI]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton,
    OfNat.ofNat_ne_one, reduceCtorEq, or_false, ee]
  norm_num
  simp only [rk5Pstar, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, smul_add,
    smul_smul, ← sq, ← pow_succ']
  module

end S70PS

open Arxiv1705_08274 S70PS in
theorem solution {N : ℕ} (S : DOModel N) (hS : S.Admissible) (h : ℝ) (hh : 0 < h) :
    (∃ e : ℕ → ℝ, ∀ (N' : ℕ) (S' : DOModel N'), S'.Admissible → ∀ t : ℝ,
      rk5Pstar S'.jacobian t = 1 + ∑ k ∈ Finset.Icc 1 6, (e k * t ^ k) • S'.jacobian ^ k) ∧
    let Ps := rk5Pstar S.jacobian h
    let P := rk5Pstar S.jacobian (-h)
    P = fromBlocks Ps.toBlocks₂₂ Ps.toBlocks₂₁ Ps.toBlocks₁₂ Ps.toBlocks₁₁ ∧
    respOfPair Ps P =
      (fromBlocks (-Ps.toBlocks₂₁) Ps.toBlocks₁₁ (-Ps.toBlocks₁₁) Ps.toBlocks₂₁)⁻¹ *
        fromBlocks (-Ps.toBlocks₁₂) Ps.toBlocks₂₂ (-Ps.toBlocks₂₂) Ps.toBlocks₁₂ ∧
    (IsUnit (Ps.toBlocks₁₁ - Ps.toBlocks₂₁).det → IsUnit (Ps.toBlocks₁₁ + Ps.toBlocks₂₁).det →
      IsSymmetricResponse (respOfPair Ps P)) := by
  refine ⟨⟨ee, fun N' S' _ t => rk5_poly _ t⟩, ?_⟩
  intro Ps P
  have hJ : swp (Dir N) * S.jacobian * swp (Dir N) = -S.jacobian := by
    rw [swp_conj, DOModel.jacobian]; simp [fromBlocks_neg]
  have h2 : P = fromBlocks Ps.toBlocks₂₂ Ps.toBlocks₂₁ Ps.toBlocks₁₂ Ps.toBlocks₁₁ := by
    rw [← swp_conj]
    simp only [Ps, P, rk5_poly, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, swp_sq,
      Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [swp_pow, hJ, show -S.jacobian = (-1 : ℝ) • S.jacobian by simp, smul_pow, smul_smul]
    congr 1
    rw [neg_pow]; ring
  have h3 : respOfPair Ps P =
      (fromBlocks (-Ps.toBlocks₂₁) Ps.toBlocks₁₁ (-Ps.toBlocks₁₁) Ps.toBlocks₂₁)⁻¹ *
        fromBlocks (-Ps.toBlocks₁₂) Ps.toBlocks₂₂ (-Ps.toBlocks₂₂) Ps.toBlocks₁₂ := by
    rw [respOfPair, h2]; simp
  refine ⟨h2, h3, fun _ _ => ?_⟩
  rw [h3]; exact resp_form Ps
