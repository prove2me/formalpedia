-- Prove2me | solution 1 for AnaliseDeFourier.coeffC_eq
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:41:50.313428+00:00
-- url     : https://prove2.me/submissions/7c94283d-5670-4d31-b790-6262a00db82e

import Mathlib
import Definitions.Def_analise_de_fourier_core

open MeasureTheory
open AnaliseDeFourier

theorem solution (T : ℝ) (hT : 0 < T) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume 0 T) (n : ℤ) :
    coeffC T (fun t => (f t : ℂ)) n
      = ((coeffA T f n : ℂ) - Complex.I * (coeffB T f n : ℂ)) / 2 := by
  have hc : IntervalIntegrable (fun t => f t * Real.cos (angFreq T n * t)) volume 0 T :=
    hf.mul_continuousOn (by fun_prop)
  have hs : IntervalIntegrable (fun t => f t * Real.sin (angFreq T n * t)) volume 0 T :=
    hf.mul_continuousOn (by fun_prop)
  have hpt : ∀ t : ℝ, (f t : ℂ) * Complex.exp (-(Complex.I * (angFreq T n * t)))
      = ((f t * Real.cos (angFreq T n * t) : ℝ) : ℂ)
        - Complex.I * ((f t * Real.sin (angFreq T n * t) : ℝ) : ℂ) := by
    intro t
    rw [show -(Complex.I * ((angFreq T n : ℂ) * t)) = ((-(angFreq T n * t) : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    rw [Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  have hc' : IntervalIntegrable (fun t => ((f t * Real.cos (angFreq T n * t) : ℝ) : ℂ)) volume 0 T :=
    ⟨hc.1.ofReal, hc.2.ofReal⟩
  have hs' : IntervalIntegrable (fun t => ((f t * Real.sin (angFreq T n * t) : ℝ) : ℂ)) volume 0 T :=
    ⟨hs.1.ofReal, hs.2.ofReal⟩
  unfold coeffC coeffA coeffB
  simp_rw [hpt]
  rw [intervalIntegral.integral_sub hc' (hs'.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal]
  push_cast
  field_simp
