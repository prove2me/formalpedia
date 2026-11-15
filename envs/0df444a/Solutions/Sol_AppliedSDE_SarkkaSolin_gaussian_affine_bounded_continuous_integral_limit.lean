-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.gaussian_affine_bounded_continuous_integral_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:11:17.654236+00:00
-- url     : https://prove2.me/submissions/2e6bbde9-2bd6-4090-b61c-a91d85ddffcc

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
set_option autoImplicit false
theorem solution
    (b q y : ℝ) (hq : 0 < q)
    (f : ℝ -> ℝ) (hf : Continuous f)
    (hfb : ∃ C : ℝ, ∀ x : ℝ, |f x| ≤ C) :
    Tendsto
      (fun h : ℝ => ∫ z : ℝ,
        f (Real.sqrt (q * h) * z + (y + b * h))
          ∂(gaussianReal 0 1))
      (𝓝[>] (0 : ℝ)) (𝓝 (f y)) := by
  let F : ℝ -> ℝ -> ℝ := fun h z =>
    f (Real.sqrt (q * h) * z + (y + b * h))
  have hmeas : ∀ᶠ h in (𝓝[>] (0 : ℝ)),
      AEStronglyMeasurable (F h) (gaussianReal 0 1) := by
    apply Filter.Eventually.of_forall
    intro h
    exact (hf.measurable.comp (by fun_prop)).aestronglyMeasurable
  obtain ⟨C, hC⟩ := hfb
  have hbound : ∃ M : ℝ, ∀ᶠ h in (𝓝[>] (0 : ℝ)),
      ∀ᵐ z ∂(gaussianReal 0 1), ‖F h z‖ ≤ M := by
    refine ⟨C, Filter.Eventually.of_forall ?_⟩
    intro h
    apply ae_of_all
    intro z
    simpa only [Real.norm_eq_abs] using hC (Real.sqrt (q * h) * z + (y + b * h))
  have hpoint : ∀ᵐ z ∂(gaussianReal 0 1),
      Tendsto (fun h : ℝ => F h z)
        (𝓝[>] (0 : ℝ)) (𝓝 (f y)) := by
    apply ae_of_all
    intro z
    have hcont : ContinuousAt (fun h : ℝ => F h z) 0 := by
      dsimp [F]
      fun_prop
    have hz : F 0 z = f y := by simp [F]
    simpa only [hz] using
      hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := tendsto_integral_filter_of_norm_le_const
    (F := F) (f := fun _ : ℝ => f y)
    (l := (𝓝[>] (0 : ℝ))) (μ := gaussianReal 0 1)
    hmeas hbound hpoint
  simpa [F] using hlim
