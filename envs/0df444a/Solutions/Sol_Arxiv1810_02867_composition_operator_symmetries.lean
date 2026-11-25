-- Prove2me | solution 1 for Arxiv1810_02867.composition_operator_symmetries
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T21:03:39.021139+00:00
-- url     : https://prove2.me/submissions/c9e85c12-28de-41cc-ad63-7e711cee19ad

import Mathlib
import Definitions.Def_Arxiv1810_02867_Basic

open MeasureTheory Matrix

theorem solution (alpha : ℝ) (beta : Fin 2 → Fin 2 → ℝ)
    (gamma : Fin 2 → ℝ) (halpha : 0 < alpha) (hsym : beta 0 1 = beta 1 0) (hb11 : 0 < beta 0 0)
    (hdet : 0 < (Matrix.of beta).det) :
    (∀ s1 : ℝ, (s1 - gamma 0) ^ 2 ≠ alpha / Arxiv1810_02867.bCoef beta 0 →
      (Arxiv1810_02867.Ltilde alpha beta (-gamma) (-s1))ᵀ * Arxiv1810_02867.Nmat *
        Arxiv1810_02867.Ltilde alpha beta gamma s1 = -Arxiv1810_02867.Nmat) ∧
    (∀ s1 : ℝ, (s1 - gamma 0) ^ 2 < alpha / Arxiv1810_02867.bCoef beta 0 →
      (Arxiv1810_02867.Ltilde alpha beta gamma s1)ᴴ * Arxiv1810_02867.Kmat *
        Arxiv1810_02867.Ltilde alpha beta gamma s1 = Arxiv1810_02867.Jmat) := by
  open Arxiv1810_02867 in
  have hD : (Matrix.of beta).det = beta 0 0 * beta 1 1 - beta 0 1 * beta 1 0 := by
    rw [Matrix.det_fin_two]; simp
  have hDne : (Matrix.of beta).det ≠ 0 := hdet.ne'
  have hθ11 : thetaOf beta 1 1 = beta 0 0 / (Matrix.of beta).det := by
    unfold thetaOf
    rw [Matrix.inv_def, Matrix.adjugate_fin_two]
    simp [Ring.inverse_eq_inv']; ring
  have hb : bCoef beta 0 = 1 / beta 0 0 := by
    unfold bCoef thetaOf
    rw [Matrix.inv_def, Matrix.adjugate_fin_two]
    simp only [Ring.inverse_eq_inv', Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      smul_eq_mul, Matrix.head_cons]
    rw [hD] at hDne ⊢
    field_simp
  have ht : 0 < thetaOf beta 1 1 := by rw [hθ11]; positivity
  have hbp : 0 < bCoef beta 0 := by rw [hb]; positivity
  have hS2 : ∀ s1 : ℝ, (s3 alpha beta gamma s1) ^ 2 = ((s3sq alpha beta gamma s1 : ℝ) : ℂ) := by
    intro s1
    unfold s3 s3sq
    split_ifs with h
    · have : 0 ≤ (thetaOf beta 1 1)⁻¹ * (alpha - bCoef beta 0 * (s1 - gamma 0) ^ 2) := by
        apply mul_nonneg (inv_nonneg.mpr ht.le)
        have := (le_div_iff₀ hbp).mp h; linarith
      rw [← Complex.ofReal_pow, Real.sq_sqrt this]
    · have : 0 ≤ (thetaOf beta 1 1)⁻¹ * (bCoef beta 0 * (s1 - gamma 0) ^ 2 - alpha) := by
        apply mul_nonneg (inv_nonneg.mpr ht.le)
        have := (div_lt_iff₀ hbp).mp (lt_of_not_ge h); linarith
      rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt this]
      push_cast; ring
  have hσ0 : ∀ s1 : ℝ, (s1 - gamma 0) ^ 2 ≠ alpha / bCoef beta 0 →
      sqrtTS alpha beta gamma s1 ≠ 0 := by
    intro s1 hs
    have hS0 : s3 alpha beta gamma s1 ≠ 0 := by
      intro h0
      have h1 : ((s3sq alpha beta gamma s1 : ℝ) : ℂ) = 0 := by rw [← hS2, h0]; ring
      have h2 : s3sq alpha beta gamma s1 = 0 := by exact_mod_cast h1
      unfold s3sq at h2
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact (inv_ne_zero ht.ne') h3
      · apply hs
        rw [eq_div_iff hbp.ne']; linarith
    have hσ2 : (sqrtTS alpha beta gamma s1) ^ 2 =
        ((thetaOf beta 1 1 : ℝ) : ℂ) * s3 alpha beta gamma s1 := by
      unfold sqrtTS
      have := Complex.cpow_nat_inv_pow (((thetaOf beta 1 1 : ℝ) : ℂ) * s3 alpha beta gamma s1)
        (n := 2) (by norm_num)
      simpa using this
    intro h0
    have : ((thetaOf beta 1 1 : ℝ) : ℂ) * s3 alpha beta gamma s1 = 0 := by rw [← hσ2, h0]; ring
    rcases mul_eq_zero.mp this with h | h
    · exact ht.ne' (by exact_mod_cast h)
    · exact hS0 h
  have hr2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hr0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    intro h; rw [h] at hr2; norm_num at hr2
  refine ⟨?_, ?_⟩
  · intro s1 hs
    have hsame : sqrtTS alpha beta (-gamma) (-s1) = sqrtTS alpha beta gamma s1 := by
      unfold sqrtTS s3
      have : (-s1 - (-gamma) 0) ^ 2 = (s1 - gamma 0) ^ 2 := by simp; ring
      rw [this]
    have h0 := hσ0 s1 hs
    unfold Ltilde Nmat
    rw [hsame]
    set σ := sqrtTS alpha beta gamma s1
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> (try field_simp) <;>
      (try first | ring | linear_combination hr2 | linear_combination (-1:ℂ) * hr2 |
        linear_combination (-2:ℂ) * hr2 | linear_combination (2:ℂ) * hr2)
    all_goals simp [hr2]
  · intro s1 hs
    have h0 := hσ0 s1 hs.ne
    have hpos : 0 < (thetaOf beta 1 1)⁻¹ * (alpha - bCoef beta 0 * (s1 - gamma 0) ^ 2) := by
      apply mul_pos (inv_pos.mpr ht)
      have := (lt_div_iff₀ hbp).mp hs; linarith
    have hSr : s3 alpha beta gamma s1 =
        ((Real.sqrt ((thetaOf beta 1 1)⁻¹ * (alpha - bCoef beta 0 * (s1 - gamma 0) ^ 2)) : ℝ) : ℂ) := by
      unfold s3; rw [if_pos hs.le]
    have hσr : sqrtTS alpha beta gamma s1 = ((((thetaOf beta 1 1) *
        Real.sqrt ((thetaOf beta 1 1)⁻¹ * (alpha - bCoef beta 0 * (s1 - gamma 0) ^ 2))) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
      unfold sqrtTS
      rw [hSr, Complex.ofReal_cpow (by positivity)]
      push_cast; rfl
    have hc : star (sqrtTS alpha beta gamma s1) = sqrtTS alpha beta gamma s1 := by
      rw [hσr]; exact Complex.conj_ofReal _
    unfold Ltilde Kmat Jmat
    set σ := sqrtTS alpha beta gamma s1
    have hc' : (starRingEnd ℂ) σ = σ := hc
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, hc'] <;> (try field_simp) <;>
      (try first | ring | linear_combination hr2 | linear_combination (-1:ℂ) * hr2 |
        linear_combination (-2:ℂ) * hr2 | linear_combination (2:ℂ) * hr2)
    all_goals simp [hr2]
