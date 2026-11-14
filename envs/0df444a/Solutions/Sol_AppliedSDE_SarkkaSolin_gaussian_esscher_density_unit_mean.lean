-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.gaussian_esscher_density_unit_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:08:14.009744+00:00
-- url     : https://prove2.me/submissions/264e090d-a01d-434d-b987-e470f8dc4529

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem solution
    (v : ℝ≥0) (theta : ℝ) :
    (∫ x : ℝ, Real.exp (theta * x - (v : ℝ) * theta ^ 2 / 2)
      ∂(gaussianReal 0 v)) = 1 := by
  have hm :
      (∫ x : ℝ, Real.exp (theta * x) ∂(gaussianReal 0 v)) =
        Real.exp ((v : ℝ) * theta ^ 2 / 2) := by
    have h := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := v)) theta
    simpa only [mgf, zero_mul, zero_add] using h
  calc
    (∫ x : ℝ, Real.exp (theta * x - (v : ℝ) * theta ^ 2 / 2)
      ∂(gaussianReal 0 v)) =
        ∫ x : ℝ,
          Real.exp (-(v : ℝ) * theta ^ 2 / 2) *
            Real.exp (theta * x) ∂(gaussianReal 0 v) := by
              apply integral_congr_ae
              filter_upwards [] with x
              rw [← Real.exp_add]
              congr 1
              ring
    _ = Real.exp (-(v : ℝ) * theta ^ 2 / 2) *
          (∫ x : ℝ, Real.exp (theta * x) ∂(gaussianReal 0 v)) := by
            rw [integral_const_mul]
    _ = 1 := by
      rw [hm, ← Real.exp_add]
      convert Real.exp_zero using 1 <;> ring