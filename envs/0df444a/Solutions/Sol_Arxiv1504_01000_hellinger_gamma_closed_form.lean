-- Prove2me | solution 1 for Arxiv1504_01000.hellinger_gamma_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T22:58:09.944885+00:00
-- url     : https://prove2.me/submissions/71432aa1-4119-4dcd-870b-4250261d8e2f

import Mathlib
import Definitions.Def_Arxiv1504_01000_Basic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace S72HG

lemma gamma_int {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    Integrable (gammaPDFReal a r) ∧ ∫ x, gammaPDFReal a r x = 1 := by
  have hm : AEMeasurable (gammaPDF a r) := by
    unfold gammaPDF; exact (measurable_gammaPDFReal a r).ennreal_ofReal.aemeasurable
  have e : ∀ x, (gammaPDF a r x).toReal = gammaPDFReal a r x := fun x => by
    unfold gammaPDF; exact ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x)
  have h1 := lintegral_gammaPDF_eq_one ha hr
  constructor
  · have := integrable_toReal_of_lintegral_ne_top hm (by rw [h1]; exact ENNReal.one_ne_top)
    simpa only [e] using this
  · have := integral_toReal hm (Filter.Eventually.of_forall (fun x => by
      unfold gammaPDF; exact ENNReal.ofReal_lt_top))
    simp only [e] at this
    rw [this, h1]; simp

lemma pointwise {L ri rj : ℝ} (hL : 0 < L) (hi : 0 < ri) (hj : 0 < rj) (x : ℝ) :
    Real.sqrt (gammaPDFReal L ri x * gammaPDFReal L rj x) =
      (Real.sqrt (ri * rj) / ((ri + rj) / 2)) ^ L * gammaPDFReal L ((ri + rj) / 2) x := by
  unfold gammaPDFReal
  split_ifs with hx
  · have hG : 0 < Real.Gamma L := Real.Gamma_pos_of_pos hL
    have hρ : 0 < (ri + rj) / 2 := by positivity
    have hs : 0 < Real.sqrt (ri * rj) := Real.sqrt_pos.2 (mul_pos hi hj)
    rw [Real.div_rpow hs.le hρ.le]
    have hxp : 0 ≤ x ^ (L - 1) := Real.rpow_nonneg hx _
    have key : ri ^ L / Real.Gamma L * x ^ (L - 1) * Real.exp (-(ri * x)) *
        (rj ^ L / Real.Gamma L * x ^ (L - 1) * Real.exp (-(rj * x))) =
        (Real.sqrt (ri * rj) ^ L / ((ri + rj) / 2) ^ L *
          (((ri + rj) / 2) ^ L / Real.Gamma L * x ^ (L - 1) * Real.exp (-((ri + rj) / 2 * x)))) ^ 2 := by
      have e1 : Real.sqrt (ri * rj) ^ L * Real.sqrt (ri * rj) ^ L = ri ^ L * rj ^ L := by
        rw [← Real.mul_rpow hs.le hs.le, Real.mul_self_sqrt (mul_pos hi hj).le,
          Real.mul_rpow hi.le hj.le]
      have e2 : Real.exp (-((ri + rj) / 2 * x)) * Real.exp (-((ri + rj) / 2 * x)) =
          Real.exp (-(ri * x)) * Real.exp (-(rj * x)) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      have hρL : 0 < ((ri + rj) / 2) ^ L := Real.rpow_pos_of_pos hρ L
      have e3 : Real.sqrt (ri * rj) ^ L / ((ri + rj) / 2) ^ L *
          (((ri + rj) / 2) ^ L / Real.Gamma L * x ^ (L - 1) * Real.exp (-((ri + rj) / 2 * x))) =
          Real.sqrt (ri * rj) ^ L / Real.Gamma L * x ^ (L - 1) * Real.exp (-((ri + rj) / 2 * x)) := by
        field_simp
      rw [e3]
      rw [show (Real.sqrt (ri * rj) ^ L / Real.Gamma L * x ^ (L - 1) *
          Real.exp (-((ri + rj) / 2 * x))) ^ 2 =
          (Real.sqrt (ri * rj) ^ L * Real.sqrt (ri * rj) ^ L) / (Real.Gamma L * Real.Gamma L) *
          (x ^ (L - 1) * x ^ (L - 1)) *
          (Real.exp (-((ri + rj) / 2 * x)) * Real.exp (-((ri + rj) / 2 * x))) by ring, e1, e2]
      ring
    rw [key, Real.sqrt_sq]
    have := Real.rpow_nonneg hs.le L
    have := Real.rpow_nonneg hρ.le L
    positivity
  · simp

end S72HG

open Arxiv1504_01000 S72HG in
theorem solution (L σi σj : ℝ) (hL : 0 < L) (hi : 0 < σi) (hj : 0 < σj) :
    Integrable (fun x => Real.sqrt (intensityPDF L (σi ^ 2) x * intensityPDF L (σj ^ 2) x)) ∧
    hellingerDist (intensityPDF L (σi ^ 2)) (intensityPDF L (σj ^ 2)) =
      1 - (2 * σi * σj / (σi ^ 2 + σj ^ 2)) ^ L := by
  have hri : 0 < L / σi ^ 2 := by positivity
  have hrj : 0 < L / σj ^ 2 := by positivity
  have hρ : 0 < (L / σi ^ 2 + L / σj ^ 2) / 2 := by positivity
  obtain ⟨hI, h1⟩ := gamma_int hL hρ
  have hp : (fun x => Real.sqrt (intensityPDF L (σi ^ 2) x * intensityPDF L (σj ^ 2) x)) =
      fun x => (Real.sqrt (L / σi ^ 2 * (L / σj ^ 2)) / ((L / σi ^ 2 + L / σj ^ 2) / 2)) ^ L *
        gammaPDFReal L ((L / σi ^ 2 + L / σj ^ 2) / 2) x := by
    funext x; unfold intensityPDF; exact pointwise hL hri hrj x
  have hK : Real.sqrt (L / σi ^ 2 * (L / σj ^ 2)) / ((L / σi ^ 2 + L / σj ^ 2) / 2) =
      2 * σi * σj / (σi ^ 2 + σj ^ 2) := by
    have : L / σi ^ 2 * (L / σj ^ 2) = (L / (σi * σj)) ^ 2 := by field_simp
    rw [this, Real.sqrt_sq (by positivity)]
    field_simp
    ring
  refine ⟨by rw [hp]; exact hI.const_mul _, ?_⟩
  unfold hellingerDist
  rw [hp, integral_const_mul, h1, hK, mul_one]
