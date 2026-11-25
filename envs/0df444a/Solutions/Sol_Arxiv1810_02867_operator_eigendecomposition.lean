-- Prove2me | solution 1 for Arxiv1810_02867.operator_eigendecomposition
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T21:01:56.243737+00:00
-- url     : https://prove2.me/submissions/99fb6ef3-ef33-455c-935c-e67ee68da1f7

import Mathlib
import Definitions.Def_Arxiv1810_02867_Basic

open MeasureTheory Matrix

theorem solution (ω alpha : ℝ) (beta : Fin 2 → Fin 2 → ℝ) (gamma : Fin 2 → ℝ)
    (s1 : ℝ) (halpha : 0 < alpha) (hsym : beta 0 1 = beta 1 0) (hb11 : 0 < beta 0 0)
    (hdet : 0 < (Matrix.of beta).det) (hs : (s1 - gamma 0) ^ 2 ≠ alpha / Arxiv1810_02867.bCoef beta 0) :
    (Arxiv1810_02867.Ltilde alpha beta gamma s1)⁻¹ = Arxiv1810_02867.LtildeInv alpha beta gamma s1 ∧
    Arxiv1810_02867.Atilde ω alpha beta gamma s1 =
      Arxiv1810_02867.Ltilde alpha beta gamma s1 * Arxiv1810_02867.Htilde ω alpha beta gamma s1 *
        (Arxiv1810_02867.Ltilde alpha beta gamma s1)⁻¹ := by
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
  set x := (s1 - gamma 0) ^ 2 with hx
  have hS2 : (s3 alpha beta gamma s1) ^ 2 = ((s3sq alpha beta gamma s1 : ℝ) : ℂ) := by
    unfold s3 s3sq
    split_ifs with h
    · have : 0 ≤ (thetaOf beta 1 1)⁻¹ * (alpha - bCoef beta 0 * x) := by
        apply mul_nonneg (inv_nonneg.mpr ht.le)
        have := (le_div_iff₀ hbp).mp h; linarith
      rw [← Complex.ofReal_pow, Real.sq_sqrt this]
    · have : 0 ≤ (thetaOf beta 1 1)⁻¹ * (bCoef beta 0 * x - alpha) := by
        apply mul_nonneg (inv_nonneg.mpr ht.le)
        have := (div_lt_iff₀ hbp).mp (lt_of_not_ge h); linarith
      rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt this]
      simp only [hx]; push_cast; ring
  have hS0 : s3 alpha beta gamma s1 ≠ 0 := by
    intro h0
    have h1 : ((s3sq alpha beta gamma s1 : ℝ) : ℂ) = 0 := by rw [← hS2, h0]; ring
    have h2 : s3sq alpha beta gamma s1 = 0 := by exact_mod_cast h1
    unfold s3sq at h2
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact (inv_ne_zero ht.ne') h3
    · apply hs
      rw [eq_div_iff hbp.ne']; linarith
  set S := s3 alpha beta gamma s1 with hSdef
  set t := thetaOf beta 1 1 with htdef
  have hσ2 : (sqrtTS alpha beta gamma s1) ^ 2 = (t : ℂ) * S := by
    unfold sqrtTS
    rw [← hSdef, ← htdef]
    have := Complex.cpow_nat_inv_pow ((t : ℂ) * S) (n := 2) (by norm_num)
    simpa using this
  have hσ0 : sqrtTS alpha beta gamma s1 ≠ 0 := by
    intro h0
    have : (t : ℂ) * S = 0 := by rw [← hσ2, h0]; ring
    rcases mul_eq_zero.mp this with h | h
    · exact ht.ne' (by exact_mod_cast h)
    · exact hS0 h
  set σ := sqrtTS alpha beta gamma s1 with hσdef
  have hr2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hr0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    intro h; rw [h] at hr2; norm_num at hr2
  have hmul : Ltilde alpha beta gamma s1 * LtildeInv alpha beta gamma s1 = 1 := by
    unfold Ltilde LtildeInv
    rw [← hσdef]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> first | linear_combination hr2 | linear_combination (-1:ℂ) * hr2 | linear_combination (-2:ℂ) * hr2
  have hinv : (Ltilde alpha beta gamma s1)⁻¹ = LtildeInv alpha beta gamma s1 :=
    Matrix.inv_eq_right_inv hmul
  refine ⟨hinv, ?_⟩
  rw [hinv]
  unfold Atilde Ltilde LtildeInv Htilde lamPM
  rw [← hσdef, ← hSdef, ← htdef]
  have hS2' : S ^ 2 = ((s3sq alpha beta gamma s1 : ℝ) : ℂ) := hS2
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp
  all_goals rw [hr2]
  · ring
  · linear_combination (2 * (ω:ℂ)) * hσ2
  · linear_combination (-2 * (ω:ℂ) * S) * hσ2 + (-2 * (ω:ℂ) * (t:ℂ)) * hS2'
  · ring
