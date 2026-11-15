-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.likelihood_tilt_pushforward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:25:55.517204+00:00
-- url     : https://prove2.me/submissions/817c90a4-03bb-4c87-9363-0b1ad33e0a37

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory
open scoped ENNReal

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (X : Ω → E) (hX : Measurable X)
    (f : E → ℝ≥0∞) (hf : Measurable f) :
    (P.withDensity (fun ω => f (X ω))).map X =
      (P.map X).withDensity f := by
  ext s hs
  rw [Measure.map_apply hX hs]
  rw [withDensity_apply (fun ω => f (X ω)) (hX hs), withDensity_apply f hs]
  have hi : Measurable (s.indicator f) := hf.indicator hs
  calc
    (∫⁻ ω in X ⁻¹' s, f (X ω) ∂P) =
      ∫⁻ ω, (s.indicator f) (X ω) ∂P := by
        rw [← lintegral_indicator (hX hs)]
        congr 1
    _ = ∫⁻ x, s.indicator f x ∂(P.map X) :=
      (lintegral_map hi hX).symm
    _ = ∫⁻ x in s, f x ∂(P.map X) := by
      rw [lintegral_indicator hs]
