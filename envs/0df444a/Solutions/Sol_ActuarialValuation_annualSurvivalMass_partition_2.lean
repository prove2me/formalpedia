-- Prove2me | solution 2 for ActuarialValuation.annualSurvivalMass_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:19:00.428985+00:00
-- url     : https://prove2.me/submissions/085d5b58-8e83-4421-a2e7-094b955538fb

import Mathlib
import Definitions.Def_actuarial_annualDeathMass
import Definitions.Def_actuarial_annualSurvivalMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K) (t : ℕ) :
    annualSurvivalMass P K t =
      annualDeathMass P K t + annualSurvivalMass P K (t + 1) := by
  have hpart : {ω : Ω | t ≤ K ω} =
      {ω : Ω | K ω = t} ∪ {ω : Ω | t + 1 ≤ K ω} := by
    ext ω
    simp only [Set.mem_union, Set.mem_setOf_eq]
    omega
  have hdisj : Disjoint {ω : Ω | K ω = t} {ω : Ω | t + 1 ≤ K ω} := by
    apply Set.disjoint_left.mpr
    intro ω ha hb
    simp only [Set.mem_setOf_eq] at *
    omega
  have hmeas : MeasurableSet {ω : Ω | t + 1 ≤ K ω} := by
    change MeasurableSet (K ⁻¹' Set.Ici (t + 1))
    exact hK measurableSet_Ici
  unfold annualSurvivalMass annualDeathMass
  rw [hpart, measure_union hdisj hmeas]
  exact ENNReal.toReal_add (measure_ne_top P _) (measure_ne_top P _)
