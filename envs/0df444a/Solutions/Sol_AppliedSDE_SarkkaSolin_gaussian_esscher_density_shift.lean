-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.gaussian_esscher_density_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:17:09.449603+00:00
-- url     : https://prove2.me/submissions/775ed132-4463-4c57-9155-d08fe4c56835

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open ProbabilityTheory
open scoped NNReal ENNReal

theorem solution
    (v : ℝ≥0) (hv : 0 < v) (theta x : ℝ) :
    gaussianPDFReal ((v : ℝ) * theta) v x =
      gaussianPDFReal 0 v x *
        Real.exp (theta * x - (v : ℝ) * theta ^ 2 / 2) := by
  have hvreal : 0 < (v : ℝ) := NNReal.coe_pos.mpr hv
  have hvne : (v : ℝ) ≠ 0 := ne_of_gt hvreal
  have hexp :
      -((x - (v : ℝ) * theta) ^ 2) / (2 * (v : ℝ)) =
        -(x ^ 2) / (2 * (v : ℝ)) +
          (theta * x - (v : ℝ) * theta ^ 2 / 2) := by
    field_simp [hvne]
    ring
  unfold gaussianPDFReal
  simp only [sub_zero]
  rw [hexp, Real.exp_add]
  ring