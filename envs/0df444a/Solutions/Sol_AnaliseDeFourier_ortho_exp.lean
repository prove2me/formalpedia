-- Prove2me | solution 1 for AnaliseDeFourier.ortho_exp
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T22:24:51.544535+00:00
-- url     : https://prove2.me/submissions/71a2fdb6-b2b4-4188-8351-12586d99805c

import Mathlib
import Definitions.Def_analise_de_fourier_core

set_option autoImplicit false
open MeasureTheory

namespace FourierAux
open AnaliseDeFourier

lemma angFreq_mul_T (T : ℝ) (hT : 0 < T) (k : ℤ) : angFreq T k * T = k * (2 * Real.pi) := by
  unfold angFreq; field_simp

lemma angFreq_eq_zero (T : ℝ) (hT : 0 < T) (k : ℤ) : angFreq T k = 0 ↔ k = 0 := by
  unfold angFreq
  have hπ := Real.pi_pos
  constructor
  · intro h
    have h2 : (2 * Real.pi * k) = 0 := by
      rcases div_eq_zero_iff.mp h with h | h
      · exact h
      · linarith
    have : (k : ℝ) = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · linarith
      · exact h
    exact_mod_cast this
  · intro h; simp [h]

lemma sin_int_two_pi (k : ℤ) : Real.sin (k * (2 * Real.pi)) = 0 :=
  Real.sin_eq_zero_iff.mpr ⟨2 * k, by push_cast; ring⟩

lemma integral_sin (T : ℝ) (hT : 0 < T) (k : ℤ) :
    ∫ t in (0 : ℝ)..T, Real.sin (angFreq T k * t) = 0 := by
  by_cases hk : k = 0
  · simp [hk, angFreq]
  have hc : angFreq T k ≠ 0 := (angFreq_eq_zero T hT k).not.mpr hk
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) hc, _root_.integral_sin,
    mul_zero, angFreq_mul_T T hT k, Real.cos_int_mul_two_pi, Real.cos_zero, sub_self, smul_zero]

lemma integral_cos (T : ℝ) (hT : 0 < T) (k : ℤ) :
    ∫ t in (0 : ℝ)..T, Real.cos (angFreq T k * t) = if k = 0 then T else 0 := by
  by_cases hk : k = 0
  · simp [hk, angFreq]
  have hc : angFreq T k ≠ 0 := (angFreq_eq_zero T hT k).not.mpr hk
  rw [if_neg hk, intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc, _root_.integral_cos,
    mul_zero, angFreq_mul_T T hT k, sin_int_two_pi, Real.sin_zero, sub_self, smul_zero]

lemma lin (T : ℝ) (n m : ℤ) (t : ℝ) :
    angFreq T n * t - angFreq T m * t = angFreq T (n - m) * t ∧
      angFreq T n * t + angFreq T m * t = angFreq T (n + m) * t := by
  unfold angFreq; push_cast; constructor <;> ring

lemma ii_cos (T : ℝ) (k : ℤ) : IntervalIntegrable (fun t => Real.cos (angFreq T k * t)) volume 0 T :=
  (by fun_prop : Continuous fun t => Real.cos (angFreq T k * t)).intervalIntegrable _ _

lemma ii_sin (T : ℝ) (k : ℤ) : IntervalIntegrable (fun t => Real.sin (angFreq T k * t)) volume 0 T :=
  (by fun_prop : Continuous fun t => Real.sin (angFreq T k * t)).intervalIntegrable _ _

end FourierAux

open AnaliseDeFourier FourierAux

open AnaliseDeFourier FourierAux
theorem solution (T : ℝ) (hT : 0 < T) (n m : ℤ) :
    (∫ t in (0 : ℝ)..T, Complex.exp (Complex.I * (angFreq T n * t))
        * Complex.exp (-(Complex.I * (angFreq T m * t))))
      = if n = m then (T : ℂ) else 0 := by
  have h : ∀ t : ℝ, Complex.exp (Complex.I * (angFreq T n * t))
        * Complex.exp (-(Complex.I * (angFreq T m * t))) =
      Complex.exp ((Complex.I * (angFreq T (n - m) : ℂ)) * t) := by
    intro t
    rw [← Complex.exp_add]
    congr 1
    unfold angFreq; push_cast; ring
  simp_rw [h]
  by_cases hnm : n = m
  · subst hnm; simp [angFreq]
  · have hk : n - m ≠ 0 := sub_ne_zero.mpr hnm
    have hc : (Complex.I * (angFreq T (n - m) : ℂ)) ≠ 0 := by
      refine mul_ne_zero Complex.I_ne_zero ?_
      exact_mod_cast (angFreq_eq_zero T hT (n - m)).not.mpr hk
    rw [integral_exp_mul_complex hc, if_neg hnm]
    have hT' : Complex.I * (angFreq T (n - m) : ℂ) * (T : ℂ) = ((n - m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      have := angFreq_mul_T T hT (n - m)
      have : ((angFreq T (n - m) * T : ℝ) : ℂ) = (((n - m : ℤ) : ℝ) * (2 * Real.pi) : ℝ) := by rw [this]
      push_cast at this ⊢
      linear_combination Complex.I * this
    rw [hT', Complex.exp_int_mul_two_pi_mul_I, Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_self, zero_div]
