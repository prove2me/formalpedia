-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.fpk_generator_formal_adjoint_one_dim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:31:44.649485+00:00
-- url     : https://prove2.me/submissions/1b1a0e93-c853-4d3d-a536-da8db407fac3

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_fpk_compact_drift_adjoint_integral
import Theorems.Thm_AppliedSDE_SarkkaSolin_fpk_compact_diffusion_adjoint_integral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped Topology
set_option autoImplicit false
theorem solution
    (f a p φ : ℝ → ℝ)
    (hf : ContDiff ℝ 2 f) (ha : ContDiff ℝ 2 a)
    (hp : ContDiff ℝ 2 p) (hφ : ContDiff ℝ 2 φ)
    (hφcompact : HasCompactSupport φ)
    (ha_nonneg : ∀ x : ℝ, 0 ≤ a x) :
    (∫ x : ℝ, φ x *
      (-deriv (fun y : ℝ => f y * p y) x +
        (1 / 2 : ℝ) *
          deriv (fun y : ℝ => deriv (fun z : ℝ => a z * p z) y) x)) =
    ∫ x : ℝ,
      (f x * deriv φ x +
        a x / 2 * deriv (fun y : ℝ => deriv φ y) x) * p x := by
  have hD := AppliedSDE.SarkkaSolin.fpk_compact_drift_adjoint_integral
    f p φ hf hp hφ hφcompact
  have hQ := AppliedSDE.SarkkaSolin.fpk_compact_diffusion_adjoint_integral
    a p φ ha hp hφ hφcompact
  have hPhi2 : Continuous (deriv (deriv φ)) :=
    (hφ.deriv' : ContDiff ℝ 1 (deriv φ)).continuous_deriv_one
  have hA2 : Continuous
      (fun z : ℝ => deriv (fun w => deriv (fun u => a u * p u) w) z) :=
    ((ha.mul hp).deriv' : ContDiff ℝ 1 (deriv (fun u => a u * p u)))
      |>.continuous_deriv_one
  have hIntD : Integrable (fun z : ℝ =>
      φ z * -deriv (fun u => f u * p u) z) :=
    (hφ.continuous.mul
      ((hf.mul hp).continuous_deriv (by norm_num)).neg)
      |>.integrable_of_hasCompactSupport hφcompact.mul_right
  have hIntQ : Integrable (fun z : ℝ =>
      φ z * (1 / 2 : ℝ) * deriv (fun w => deriv (fun u => a u * p u) w) z) :=
    ((hφ.continuous.mul continuous_const).mul hA2)
      |>.integrable_of_hasCompactSupport hφcompact.mul_right.mul_right
  have hIntR1 : Integrable (fun z : ℝ =>
      f z * deriv φ z * p z) :=
    ((hf.continuous.mul (hφ.continuous_deriv (by norm_num))).mul hp.continuous)
      |>.integrable_of_hasCompactSupport hφcompact.deriv.mul_left.mul_right
  have hIntR2 : Integrable (fun z : ℝ =>
      a z / 2 * deriv (deriv φ) z * p z) :=
    (((ha.continuous.div_const 2).mul hPhi2).mul hp.continuous)
      |>.integrable_of_hasCompactSupport hφcompact.deriv.deriv.mul_left.mul_right
  simp_rw [mul_add, add_mul, ← mul_assoc]
  rw [integral_add hIntD hIntQ, integral_add hIntR1 hIntR2, hD, hQ]
