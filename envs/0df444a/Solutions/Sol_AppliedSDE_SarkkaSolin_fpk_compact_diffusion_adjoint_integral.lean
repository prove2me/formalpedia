-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.fpk_compact_diffusion_adjoint_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:30:13.090125+00:00
-- url     : https://prove2.me/submissions/95f0c66c-f5c1-425b-af4e-d99eb84ffedc

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AppliedSDE_SarkkaSolin_compact_second_ibp_one_dim
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
set_option autoImplicit false
theorem solution
    (a p φ : ℝ -> ℝ)
    (ha : ContDiff ℝ 2 a) (hp : ContDiff ℝ 2 p)
    (hφ : ContDiff ℝ 2 φ)
    (hφcompact : HasCompactSupport φ) :
    (∫ z : ℝ, φ z * (1 / 2 : ℝ) *
      deriv (fun w => deriv (fun u => a u * p u) w) z) =
      (∫ z : ℝ, a z / 2 * deriv (fun w => deriv φ w) z * p z) := by
  have hA : ContDiff ℝ 2 (fun w : ℝ => a w * p w) :=
    ha.mul hp
  have hsecond := AppliedSDE.SarkkaSolin.compact_second_ibp_one_dim
    φ (fun w => a w * p w) hφ hA hφcompact
  have heq : (fun z : ℝ => φ z * (1 / 2 : ℝ) *
      deriv (fun w => deriv (fun u => a u * p u) w) z) =
      (fun z => (1 / 2 : ℝ) * (φ z *
        deriv (fun w => deriv (fun u => a u * p u) w) z)) := by
    funext z
    ring
  calc
    _ = (1 / 2 : ℝ) *
      (∫ z : ℝ, φ z *
        deriv (fun w => deriv (fun u => a u * p u) w) z) := by
      rw [heq, integral_const_mul]
    _ = (1 / 2 : ℝ) *
      (∫ z : ℝ, deriv (deriv φ) z * (a z * p z)) := by
      rw [hsecond]
    _ = (∫ z : ℝ, a z / 2 * deriv (deriv φ) z * p z) := by
      rw [← integral_const_mul]
      congr 1
      funext z
      ring
