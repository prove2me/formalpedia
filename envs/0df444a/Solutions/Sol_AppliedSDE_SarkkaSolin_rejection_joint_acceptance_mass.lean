-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.rejection_joint_acceptance_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:49:19.58636+00:00
-- url     : https://prove2.me/submissions/b8a82505-074e-47c3-abf6-efc5af4f6b11

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_rejection_uniform_slice_mass
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
    ((P.prod U).restrict C) (B ×ˢ Set.univ) =
      ∫⁻ omega in B, ENNReal.ofReal (weight omega) ∂ P := by
  classical
  let U : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc 0 1)
  let C : Set (Ω × ℝ) := {z | z.2 ≤ weight z.1}
  have hC : MeasurableSet C := by
    dsimp [C]
    exact measurableSet_le measurable_snd (hweight.comp measurable_fst)
  have hBC : MeasurableSet ((B ×ˢ Set.univ) ∩ C) :=
    (hB.prod MeasurableSet.univ).inter hC
  change ((P.prod U).restrict C) (B ×ˢ Set.univ) = _
  rw [Measure.restrict_apply (hB.prod MeasurableSet.univ)]
  rw [Measure.prod_apply hBC]
  calc
    _ = ∫⁻ omega,
          B.indicator (fun v => ENNReal.ofReal (weight v)) omega ∂ P := by
      apply lintegral_congr
      intro omega
      by_cases hm : omega ∈ B
      · have hs : Prod.mk omega ⁻¹' ((B ×ˢ Set.univ) ∩ C) =
            Set.Iic (weight omega) := by
            ext u
            simp [C, hm]
        rw [hs]
        simpa [hm, U] using
          (AppliedSDE.SarkkaSolin.rejection_uniform_slice_mass
            (weight omega) (hbound omega).1 (hbound omega).2)
      · have hs : Prod.mk omega ⁻¹' ((B ×ˢ Set.univ) ∩ C) =
            (∅ : Set ℝ) := by
            ext u
            simp [C, hm]
        rw [hs, measure_empty]
        simp [hm]
    _ = ∫⁻ omega in B, ENNReal.ofReal (weight omega) ∂ P :=
      lintegral_indicator hB _
