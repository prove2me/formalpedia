-- Prove2me | solution 1 for AnaliseDeFourier.ortho_cos_cos
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T22:24:51.598013+00:00
-- url     : https://prove2.me/submissions/f3a4ff17-105c-4a0d-9bf8-ab9f95ea4e2d

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
theorem solution (T : ℝ) (hT : 0 < T) (n m : ℕ) :
    (∫ t in (0 : ℝ)..T, Real.cos (angFreq T (n : ℤ) * t) * Real.cos (angFreq T (m : ℤ) * t))
      = if n = m then (if n = 0 then T else T / 2) else 0 := by
  have h : ∀ t, Real.cos (angFreq T (n : ℤ) * t) * Real.cos (angFreq T (m : ℤ) * t) =
      (Real.cos (angFreq T ((n : ℤ) - m) * t) + Real.cos (angFreq T ((n : ℤ) + m) * t)) / 2 := by
    intro t
    rw [← (lin T n m t).1, ← (lin T n m t).2, Real.cos_sub, Real.cos_add]; ring
  simp_rw [h]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (ii_cos T _) (ii_cos T _),
    integral_cos T hT, integral_cos T hT]
  by_cases hnm : n = m
  · subst hnm
    by_cases hn : n = 0
    · subst hn; simp
    · have : ((n : ℤ) + n) ≠ 0 := by omega
      simp [hn, this]
  · have h1 : ((n : ℤ) - m) ≠ 0 := by omega
    have h2 : ((n : ℤ) + m) ≠ 0 := by omega
    simp [hnm, h1, h2]
