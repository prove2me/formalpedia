-- Prove2me | solution 1 for Arxiv1705_08274.diamond_difference_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T05:12:26.884176+00:00
-- url     : https://prove2.me/submissions/8bfe0355-7ca3-471b-98c1-f632e0ecde8b

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

end S70PS

open Arxiv1705_08274 S70PS in
theorem solution {N : ℕ} (S : DOModel N) (hS : S.Admissible)
    (h : ℝ) (hh : 0 < h) :
    let Ps := 1 + (h / 2) • S.jacobian
    let P := 1 - (h / 2) • S.jacobian
    (Ps.toBlocks₁₁ = 1 + (h / 2) • S.alpha ∧ Ps.toBlocks₁₂ = -((h / 2) • S.beta) ∧
      Ps.toBlocks₂₁ = (h / 2) • S.beta ∧ Ps.toBlocks₂₂ = 1 - (h / 2) • S.alpha) ∧
    (Ps = padeDen S.jacobian h 1 ∧ P = padeNum S.jacobian h 1) ∧
    P = 1 + (-h / 2) • S.jacobian ∧
    P = fromBlocks Ps.toBlocks₂₂ Ps.toBlocks₂₁ Ps.toBlocks₁₂ Ps.toBlocks₁₁ ∧
    respOfPair Ps P =
      (fromBlocks (-Ps.toBlocks₂₁) Ps.toBlocks₁₁ (-Ps.toBlocks₁₁) Ps.toBlocks₂₁)⁻¹ *
        fromBlocks (-Ps.toBlocks₁₂) Ps.toBlocks₂₂ (-Ps.toBlocks₂₂) Ps.toBlocks₁₂ ∧
    (IsUnit (Ps.toBlocks₁₁ - Ps.toBlocks₂₁).det → IsUnit (Ps.toBlocks₁₁ + Ps.toBlocks₂₁).det →
      IsSymmetricResponse (respOfPair Ps P)) := by
  intro Ps P
  have hPs : Ps = fromBlocks (1 + (h / 2) • S.alpha) (-((h / 2) • S.beta)) ((h / 2) • S.beta)
      (1 - (h / 2) • S.alpha) := by
    simp only [Ps, DOModel.jacobian, ← fromBlocks_one, fromBlocks_smul, fromBlocks_add]
    congr 1 <;> simp [sub_eq_add_neg]
  have hP : P = fromBlocks (1 - (h / 2) • S.alpha) ((h / 2) • S.beta) (-((h / 2) • S.beta))
      (1 + (h / 2) • S.alpha) := by
    simp only [P, DOModel.jacobian, ← fromBlocks_one, fromBlocks_smul, sub_eq_add_neg,
      fromBlocks_neg, fromBlocks_add]
    congr 1 <;> simp
  have hc : padeCoeff 1 1 = 1 / 2 := by
    simp [padeCoeff, Nat.factorial]
  have hD : Ps = padeDen S.jacobian h 1 := by
    simp only [Ps, padeDen, Finset.Icc_self, Finset.sum_singleton, hc, pow_one]
    congr 2; ring
  have hN : P = padeNum S.jacobian h 1 := by
    simp only [P, padeNum, Finset.Icc_self, Finset.sum_singleton, hc, pow_one, sub_eq_add_neg,
      ← neg_smul]
    congr 2; ring
  have hP' : P = 1 + (-h / 2) • S.jacobian := by
    simp only [P, sub_eq_add_neg, ← neg_smul, neg_div]
  have h2 : P = fromBlocks Ps.toBlocks₂₂ Ps.toBlocks₂₁ Ps.toBlocks₁₂ Ps.toBlocks₁₁ := by
    rw [hP, hPs]; simp
  have h3 : respOfPair Ps P =
      (fromBlocks (-Ps.toBlocks₂₁) Ps.toBlocks₁₁ (-Ps.toBlocks₁₁) Ps.toBlocks₂₁)⁻¹ *
        fromBlocks (-Ps.toBlocks₁₂) Ps.toBlocks₂₂ (-Ps.toBlocks₂₂) Ps.toBlocks₁₂ := by
    rw [respOfPair, h2]; simp
  refine ⟨?_, ⟨hD, hN⟩, hP', h2, h3, fun _ _ => ?_⟩
  · rw [hPs]; simp
  · rw [h3]; exact resp_form Ps
