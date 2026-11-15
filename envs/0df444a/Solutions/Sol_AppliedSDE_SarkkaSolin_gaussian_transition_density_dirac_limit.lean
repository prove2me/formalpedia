-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.gaussian_transition_density_dirac_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T11:57:53.123602+00:00
-- url     : https://prove2.me/submissions/cbebd79c-f11e-432d-aae8-58dea4fd5d3f

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_transition_kernel_integral_eq_gaussianReal
import Theorems.Thm_AppliedSDE_SarkkaSolin_gaussianReal_expectation_narrow_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
set_option autoImplicit false
theorem solution
    (b q y s : ℝ) (hq : 0 < q)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hfb : ∃ C : ℝ, ∀ x : ℝ, |f x| ≤ C) :
    let p : ℝ → ℝ → ℝ := fun x t =>
      Real.exp (-((x - y - b * (t - s)) ^ 2 / (2 * q * (t - s)))) /
        Real.sqrt (2 * Real.pi * q * (t - s));
    Tendsto (fun h : ℝ => ∫ x : ℝ, p x (s + h) * f x)
      (𝓝[>] (0 : ℝ)) (𝓝 (f y)) := by
  intro p
  have hlimit :=
    AppliedSDE.SarkkaSolin.gaussianReal_expectation_narrow_limit
      b q y hq f hf hfb
  have heq :
      (fun h : ℝ => ∫ x : ℝ, p x (s + h) * f x) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun h : ℝ =>
        ∫ x : ℝ, f x ∂(gaussianReal (y + b * h) (q * h).toNNReal)) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hpos : 0 < h := hh
    have hqpos : 0 ≤ q * h := (mul_pos hq hpos).le
    have hv : (q * h).toNNReal =
        (⟨q * h, hqpos⟩ : ℝ≥0) := by
      apply Subtype.ext
      simp [Real.coe_toNNReal, hqpos]
    have hk :=
      AppliedSDE.SarkkaSolin.gaussian_transition_kernel_integral_eq_gaussianReal
        b q y h hq hpos f
    simpa [p, hv, add_sub_cancel_left] using hk
  exact hlimit.congr' heq.symm
