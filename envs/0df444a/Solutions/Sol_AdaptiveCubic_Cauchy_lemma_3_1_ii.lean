-- Prove2me | solution 1 for AdaptiveCubic.Cauchy.lemma_3_1_ii
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:14:09.575111+00:00
-- url     : https://prove2.me/submissions/6058682b-afb9-43f6-92c3-e36491924d3e

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_IsARCRun

set_option autoImplicit false
open scoped RealInnerProductSpace
open AdaptiveCubic.Cauchy

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hB : IsSelfAdjoint B)
    (κB : ℝ) (hκB : 0 ≤ κB) (hAM1 : ‖B‖ ≤ κB)
    (σ : ℝ) (hσ : 0 < σ) (x s : EuclideanSpace ℝ (Fin n))
    (hcauchy : ∀ α : ℝ, 0 ≤ α → model f B σ x s ≤ model f B σ x (-(α • gradient f x))) :
    ‖s‖ ≤ 3 / σ * max κB (√(σ * ‖gradient f x‖)) := by
  have h0 := hcauchy 0 le_rfl
  simp only [model, zero_smul, neg_zero, inner_zero_left, map_zero, norm_zero, add_zero,
    inner_zero_right] at h0
  have h0' : ⟪s, gradient f x⟫ + 1 / 2 * ⟪s, B s⟫ + σ / 3 * ‖s‖ ^ 3 ≤ 0 := by
    have : (0 : ℝ) ^ 3 = 0 := by norm_num
    simp only [this, mul_zero, add_zero] at h0
    linarith
  set t := ‖s‖ with ht
  set G := ‖gradient f x‖ with hG
  have ht0 : 0 ≤ t := norm_nonneg _
  have hG0 : 0 ≤ G := norm_nonneg _
  have h1 : ⟪s, gradient f x⟫ ≥ -(t * G) := by
    have := abs_real_inner_le_norm s (gradient f x)
    have := (abs_le.mp this).1
    linarith
  have h2 : ⟪s, B s⟫ ≥ -(κB * t ^ 2) := by
    have h3 := abs_real_inner_le_norm s (B s)
    have h4 : ‖B s‖ ≤ ‖B‖ * ‖s‖ := B.le_opNorm s
    have h5 : ‖B‖ * ‖s‖ ≤ κB * t := mul_le_mul_of_nonneg_right hAM1 ht0
    have h6 : ‖s‖ * ‖B s‖ ≤ t * (κB * t) := mul_le_mul_of_nonneg_left (h4.trans h5) ht0
    have := (abs_le.mp h3).1
    nlinarith
  have hmain : σ / 3 * t ^ 3 ≤ t * G + 1 / 2 * κB * t ^ 2 := by nlinarith
  set u := max κB (√(σ * G)) with hu
  have hu0 : 0 ≤ u := le_max_of_le_right (Real.sqrt_nonneg _)
  have hκu : κB ≤ u := le_max_left _ _
  have hσG : σ * G ≤ u ^ 2 := by
    have : √(σ * G) ≤ u := le_max_right _ _
    have h7 := Real.sq_sqrt (mul_nonneg hσ.le hG0)
    nlinarith [Real.sqrt_nonneg (σ * G)]
  have hgoal : t ≤ 3 / σ * u := by
    by_contra hcon
    push_neg at hcon
    have hw : 3 * u < σ * t := by
      have := mul_lt_mul_of_pos_left hcon hσ
      have e : σ * (3 / σ * u) = 3 * u := by field_simp
      linarith
    have htpos : 0 < t := by
      by_contra h; push_neg at h
      have : t = 0 := le_antisymm h ht0
      rw [this] at hcon
      have : 0 ≤ 3 / σ * u := by positivity
      linarith
    -- multiply hmain by 3σ... : (σ t)^2 / 3 ≤ σ G + κ σ t / 2 ... 
    have hA : (σ * t) ^ 2 / 3 ≤ σ * G + 1 / 2 * κB * (σ * t) := by
      have := mul_le_mul_of_nonneg_left hmain (by positivity : 0 ≤ σ / t)
      field_simp at this ⊢
      nlinarith [this]
    have hB' : (σ * t) ^ 2 / 3 ≤ u ^ 2 + 1 / 2 * u * (σ * t) := by
      have : 1 / 2 * κB * (σ * t) ≤ 1 / 2 * u * (σ * t) := by
        have : 0 ≤ σ * t := by positivity
        nlinarith
      linarith
    nlinarith [mul_pos (by linarith : 0 < σ * t - 3 * u) (by nlinarith : 0 < σ * t + 3 / 2 * u)]
  exact hgoal
