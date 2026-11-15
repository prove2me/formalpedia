-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.rejection_real_accepted_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:49:27.362715+00:00
-- url     : https://prove2.me/submissions/81e3dcf7-3c6b-499f-8572-dfa81c4051d5

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_rejection_joint_acceptance_mass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
set_option autoImplicit false
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (weight : Ω -> ℝ) (hweight : Measurable weight)
    (hbound : ∀ omega : Ω, 0 ≤ weight omega ∧ weight omega ≤ 1)
    (B : Set Ω) (hB : MeasurableSet B) :
    let U : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc 0 1)
    let C : Set (Ω × ℝ) := {z | z.2 ≤ weight z.1}
    ((P.prod U).restrict C).real (B ×ˢ Set.univ) =
      ∫ omega in B, weight omega ∂ P := by
  classical
  let U : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc 0 1)
  let C : Set (Ω × ℝ) := {z | z.2 ≤ weight z.1}
  have hmass : ((P.prod U).restrict C) (B ×ˢ Set.univ) =
      ∫⁻ omega in B, ENNReal.ofReal (weight omega) ∂ P := by
    simpa only [U, C] using
      (AppliedSDE.SarkkaSolin.rejection_joint_acceptance_mass
        P weight hweight hbound B hB)
  have hint : Integrable weight P :=
    Integrable.of_bound hweight.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun omega => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hbound omega).1]
          using (hbound omega).2)
  have hnonneg : 0 ≤ ∫ omega in B, weight omega ∂ P :=
    integral_nonneg fun omega => (hbound omega).1
  have hlin :
      ENNReal.ofReal (∫ omega in B, weight omega ∂ P) =
        ∫⁻ omega in B, ENNReal.ofReal (weight omega) ∂ P :=
    ofReal_integral_eq_lintegral_ofReal hint.integrableOn
      (Filter.Eventually.of_forall fun omega => (hbound omega).1)
  change ((P.prod U).restrict C).real (B ×ˢ Set.univ) = _
  rw [Measure.real_def, hmass, ← hlin]
  exact ENNReal.toReal_ofReal hnonneg
