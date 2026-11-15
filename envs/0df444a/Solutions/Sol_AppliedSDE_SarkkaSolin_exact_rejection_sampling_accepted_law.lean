-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.exact_rejection_sampling_accepted_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:06:19.069343+00:00
-- url     : https://prove2.me/submissions/8b114aaf-2c1c-44c2-8071-26f26a19637b

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_rejection_real_accepted_mass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (weight : Ω → ℝ) (hweight : Measurable weight)
    (hbound : ∀ ω : Ω, 0 ≤ weight ω ∧ weight ω ≤ 1)
    (hpositive : 0 < ∫ ω, weight ω ∂P)
    (A : Set Ω) (hA : MeasurableSet A) :
    let U : Measure ℝ :=
      (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)
    let joint : Measure (Ω × ℝ) := P.prod U
    let accept : Set (Ω × ℝ) := {z | z.2 ≤ weight z.1}
    (joint.restrict accept).real (A ×ˢ Set.univ) /
      (joint.restrict accept).real Set.univ =
        (∫ ω in A, weight ω ∂P) / (∫ ω, weight ω ∂P) := by
  let U : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc 0 1)
  let C : Set (Ω × ℝ) := {z | z.2 ≤ weight z.1}
  have hmassA : ((P.prod U).restrict C).real (A ×ˢ Set.univ) =
      ∫ omega in A, weight omega ∂ P := by
    simpa only [U, C] using
      (AppliedSDE.SarkkaSolin.rejection_real_accepted_mass
        P weight hweight hbound A hA)
  have hmassUniv : ((P.prod U).restrict C).real Set.univ =
      ∫ omega, weight omega ∂ P := by
    have hset : (Set.univ : Set (Ω × ℝ)) =
        Set.univ ×ˢ Set.univ := by
      ext z
      simp
    rw [hset]
    simpa [U, C] using
      (AppliedSDE.SarkkaSolin.rejection_real_accepted_mass
        P weight hweight hbound Set.univ MeasurableSet.univ)
  change ((P.prod U).restrict C).real (A ×ˢ Set.univ) /
    ((P.prod U).restrict C).real Set.univ =
    (∫ omega in A, weight omega ∂ P) /
    (∫ omega, weight omega ∂ P)
  rw [hmassA, hmassUniv]
