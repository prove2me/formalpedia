-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.girsanov_density_preserves_path_continuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:30:42.528833+00:00
-- url     : https://prove2.me/submissions/fd6b5022-cb33-45d6-8581-4f0605fe1f27

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory
open scoped ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ρ : Ω → ℝ≥0∞)
    (X : ℝ → Ω → ℝ)
    (hcont : Filter.Eventually
      (fun ω : Ω => Continuous (fun t : ℝ => X t ω)) (ae P)) :
    Filter.Eventually
      (fun ω : Ω => Continuous (fun t : ℝ => X t ω))
      (ae (P.withDensity ρ)) := by
  exact (withDensity_absolutelyContinuous P ρ).ae_le hcont
