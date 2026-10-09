-- Prove2me | solution 1 for ActuarialValuation.annualSurvivalMass_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:18:21.003384+00:00
-- url     : https://prove2.me/submissions/b89bfc2c-7034-460c-a89a-4fecf304e7a0

import Mathlib
import Definitions.Def_actuarial_annualDeathMass
import Definitions.Def_actuarial_annualSurvivalMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (K : Ω → ℕ) (hK : Measurable K) (t : ℕ)
  : annualSurvivalMass P K t =
      annualDeathMass P K t + annualSurvivalMass P K (t + 1) := by
  have hset : {ω : Ω | t ≤ K ω} =
      {ω : Ω | K ω = t} ∪ {ω : Ω | t + 1 ≤ K ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union]
    omega
  have hdisj : Disjoint {ω : Ω | K ω = t} {ω : Ω | t + 1 ≤ K ω} := by
    apply Set.disjoint_left.mpr
    intro ω hdeath hnext
    change K ω = t at hdeath
    change t + 1 ≤ K ω at hnext
    omega
  have hm : MeasurableSet {ω : Ω | t + 1 ≤ K ω} := by
    change MeasurableSet (K ⁻¹' Set.Ici (t + 1))
    exact hK measurableSet_Ici
  have hmass : P {ω : Ω | t ≤ K ω} =
      P {ω : Ω | K ω = t} + P {ω : Ω | t + 1 ≤ K ω} := by
    rw [hset, measure_union hdisj hm]
  unfold annualSurvivalMass annualDeathMass
  rw [hmass, ENNReal.toReal_add (measure_ne_top P _) (measure_ne_top P _)]
