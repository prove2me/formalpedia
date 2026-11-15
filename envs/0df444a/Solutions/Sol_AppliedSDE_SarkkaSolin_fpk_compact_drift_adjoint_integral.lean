-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.fpk_compact_drift_adjoint_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:30:06.212143+00:00
-- url     : https://prove2.me/submissions/874d4a52-5404-42b9-8f45-49b704bbb187

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_compact_ibp_one_dim
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
set_option autoImplicit false
theorem solution
    (f p φ : ℝ -> ℝ)
    (hf : ContDiff ℝ 2 f) (hp : ContDiff ℝ 2 p)
    (hφ : ContDiff ℝ 2 φ)
    (hφcompact : HasCompactSupport φ) :
    (∫ z : ℝ, φ z * -deriv (fun w => f w * p w) z) =
      (∫ z : ℝ, f z * deriv φ z * p z) := by
  have hF : ContDiff ℝ 1 (fun w : ℝ => f w * p w) :=
    (hf.mul hp).of_le (by norm_num)
  have hfirst := AppliedSDE.SarkkaSolin.compact_ibp_one_dim
    φ (fun w => f w * p w) (hφ.of_le (by norm_num))
      hF hφcompact
  calc
    _ = -(∫ z : ℝ, φ z * deriv (fun w => f w * p w) z) := by
      simp only [mul_neg, integral_neg]
    _ = (∫ z : ℝ, deriv φ z * (f z * p z)) := by
      rw [hfirst]
      ring
    _ = (∫ z : ℝ, f z * deriv φ z * p z) := by
      congr 1
      funext z
      ring
