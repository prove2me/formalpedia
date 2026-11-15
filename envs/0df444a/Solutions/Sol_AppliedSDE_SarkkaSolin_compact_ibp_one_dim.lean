-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.compact_ibp_one_dim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:24:17.037487+00:00
-- url     : https://prove2.me/submissions/710fbfb9-d53f-41b9-8d55-12b76922c6cb

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped Topology
set_option autoImplicit false
theorem solution
    (u v : ℝ -> ℝ) (hu : ContDiff ℝ 1 u)
    (hv : ContDiff ℝ 1 v) (hcompact : HasCompactSupport u) :
    (∫ x : ℝ, u x * deriv v x) =
      -(∫ x : ℝ, deriv u x * v x) := by
  have hucont : Continuous u := hu.continuous
  have hvcont : Continuous v := hv.continuous
  have huder : Continuous (deriv u) := hu.continuous_deriv_one
  have hvder : Continuous (deriv v) := hv.continuous_deriv_one
  have hI1 : Integrable (u * deriv v) :=
    (hucont.mul hvder).integrable_of_hasCompactSupport hcompact.mul_right
  have hI2 : Integrable ((deriv u) * v) :=
    (huder.mul hvcont).integrable_of_hasCompactSupport hcompact.deriv.mul_right
  have hI3 : Integrable (u * v) :=
    (hucont.mul hvcont).integrable_of_hasCompactSupport hcompact.mul_right
  exact integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := u) (v := v) (u' := deriv u) (v' := deriv v)
    (fun x _ => (hu.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => (hv.differentiable (by norm_num) x).hasDerivAt)
    hI1 hI2 hI3
