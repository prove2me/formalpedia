-- Prove2me | solution 1 for AdaptiveCubic.Cauchy.lemma_3_1_i
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:23:23.612101+00:00
-- url     : https://prove2.me/submissions/5e5b35ef-94b3-4098-be6a-954208cd4241

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_IsARCRun

set_option autoImplicit false
open scoped RealInnerProductSpace
open AdaptiveCubic.Cauchy

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hB : IsSelfAdjoint B)
    (σ : ℝ) (hσ : 0 < σ) (x s : EuclideanSpace ℝ (Fin n))
    (hcauchy : ∀ α : ℝ, 0 ≤ α → model f B σ x s ≤ model f B σ x (-(α • gradient f x))) :
    ‖gradient f x‖ / (6 * √2) *
        min (‖gradient f x‖ / (1 + ‖B‖)) (1 / 2 * √(‖gradient f x‖ / σ)) ≤
      f x - model f B σ x s := by
  set g := gradient f x with hg
  set G := ‖g‖ with hG
  set A := ‖B‖ with hA
  have hG0 : 0 ≤ G := norm_nonneg _
  have hA0 : 0 ≤ A := norm_nonneg _
  have h0 := hcauchy 0 le_rfl
  have hm0 : model f B σ x s ≤ f x := by
    simpa [model] using h0
  rcases hG0.eq_or_lt with hGz | hGp
  · rw [← hGz]
    simp only [zero_div, zero_mul]
    linarith
  -- positive gradient
  set M : ℝ := min (G / (1 + A)) (1 / 2 * √(G / σ)) with hM
  set α : ℝ := min (1 / (1 + A)) (1 / 2 * √(G / σ) / G) with hα
  have hMα : M = G * α := by
    rw [hM, hα, mul_min_of_nonneg _ _ hG0]
    congr 1
    · field_simp
    · field_simp
  have hα0 : 0 < α := by
    rw [hα]
    refine lt_min (by positivity) ?_
    have : 0 < √(G / σ) := Real.sqrt_pos.mpr (by positivity)
    positivity
  have hα1 : α * (1 + A) ≤ 1 := by
    have : α ≤ 1 / (1 + A) := min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at this
    exact this
  have hα2 : α ^ 2 * (σ * G) ≤ 1 / 4 := by
    have h1 : α ≤ 1 / 2 * √(G / σ) / G := min_le_right _ _
    have h2 : α * G ≤ 1 / 2 * √(G / σ) := by
      rw [le_div_iff₀ hGp] at h1; exact h1
    have h3 : (α * G) ^ 2 ≤ (1 / 2 * √(G / σ)) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity) h2
    have h4 : (1 / 2 * √(G / σ)) ^ 2 = 1 / 4 * (G / σ) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
    rw [h4] at h3
    have h5 : α ^ 2 * G ^ 2 ≤ 1 / 4 * (G / σ) := by nlinarith
    -- multiply by σ / G
    have h6 : α ^ 2 * (σ * G) = (α ^ 2 * G ^ 2) * (σ / G) := by field_simp
    rw [h6]
    calc (α ^ 2 * G ^ 2) * (σ / G) ≤ (1 / 4 * (G / σ)) * (σ / G) :=
          mul_le_mul_of_nonneg_right h5 (by positivity)
      _ = 1 / 4 := by field_simp
  -- the model along the steepest descent direction
  have hs' := hcauchy α hα0.le
  have hgBg : ⟪g, B g⟫ ≤ A * G ^ 2 := by
    have h3 := real_inner_le_norm g (B g)
    have h4 : ‖B g‖ ≤ ‖B‖ * ‖g‖ := B.le_opNorm g
    have : ‖g‖ * ‖B g‖ ≤ ‖g‖ * (‖B‖ * ‖g‖) := mul_le_mul_of_nonneg_left h4 hG0
    nlinarith
  have hmod : model f B σ x (-(α • g)) = f x - α * G ^ 2 + 1 / 2 * (α ^ 2 * ⟪g, B g⟫) +
      σ / 3 * (α * G) ^ 3 := by
    simp only [model, ← hg, inner_neg_left, inner_smul_left, map_neg, map_smul, inner_neg_right,
      inner_smul_right, norm_neg, norm_smul, real_inner_self_eq_norm_sq, Real.norm_eq_abs,
      abs_of_pos hα0, hG, conj_trivial]
    ring
  have hlow : (5 / 12) * (α * G ^ 2) ≤ f x - model f B σ x s := by
    rw [hmod] at hs'
    have e1 : α ^ 2 * ⟪g, B g⟫ ≤ α ^ 2 * (A * G ^ 2) := mul_le_mul_of_nonneg_left hgBg (by positivity)
    have e2 : α * A ≤ 1 - α := by nlinarith
    have e3 : σ / 3 * (α * G) ^ 3 ≤ (1 / 12) * (α * G ^ 2) := by
      have : σ / 3 * (α * G) ^ 3 = (α * G ^ 2) * (σ / 3 * (α ^ 2 * G)) := by ring
      rw [this]
      have : σ / 3 * (α ^ 2 * G) ≤ 1 / 12 := by nlinarith
      nlinarith [mul_pos hα0 (pow_pos hGp 2)]
    have e4 : 1 / 2 * (α ^ 2 * (A * G ^ 2)) ≤ 1 / 2 * (α * G ^ 2) := by
      have : α ^ 2 * (A * G ^ 2) = (α * G ^ 2) * (α * A) := by ring
      rw [this]
      nlinarith [mul_pos hα0 (pow_pos hGp 2)]
    nlinarith
  have hc : 1 / (6 * √2) ≤ 5 / 12 := by
    have : (1 : ℝ) < √2 * 1.2 := by
      have : (1.2 : ℝ) ≤ √2 * 1.2 := by nlinarith [Real.one_lt_sqrt_two]
      linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.one_lt_sqrt_two]
  calc G / (6 * √2) * M = (1 / (6 * √2)) * (α * G ^ 2) := by rw [hMα]; ring
    _ ≤ (5 / 12) * (α * G ^ 2) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ _ := hlow
