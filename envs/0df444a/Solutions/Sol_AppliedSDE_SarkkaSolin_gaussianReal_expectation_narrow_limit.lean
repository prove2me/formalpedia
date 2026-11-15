-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.gaussianReal_expectation_narrow_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:21:20.005262+00:00
-- url     : https://prove2.me/submissions/f8759bcf-328f-417f-972a-30d43fc4078e

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_gaussianReal_sqrt_variance_affine_pushforward
import Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_affine_bounded_continuous_integral_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
set_option autoImplicit false
theorem solution
    (b q y : ℝ) (hq : 0 < q)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hfb : ∃ C : ℝ, ∀ x : ℝ, |f x| ≤ C) :
    Tendsto
      (fun h : ℝ =>
        ∫ x : ℝ, f x ∂(gaussianReal (y + b * h) (q * h).toNNReal))
      (𝓝[>] (0 : ℝ)) (𝓝 (f y)) := by
  have hlim :=
    AppliedSDE.SarkkaSolin.gaussian_affine_bounded_continuous_integral_limit
      b q y hq f hf hfb
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hpush :=
    AppliedSDE.SarkkaSolin.gaussianReal_sqrt_variance_affine_pushforward
      b q y h hq hh.le
  have hphi : Measurable
      (fun z : ℝ => Real.sqrt (q * h) * z + (y + b * h)) := by
        fun_prop
  have hmap := integral_map_of_stronglyMeasurable
    (μ := gaussianReal 0 1) hphi hf.measurable.stronglyMeasurable
  rw [hpush] at hmap
  exact hmap.symm
