-- Prove2me | solution 1 for ActuarialValuation.pureEndowment_variance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:15:02.519267+00:00
-- url     : https://prove2.me/submissions/59a4e2d2-ed86-42ca-85e7-f37ae780edc5

import Mathlib
import Definitions.Def_actuarial_pureEndowmentPV
import Definitions.Def_actuarial_strictSurvivalEvent
import Definitions.Def_actuarial_presentValue
import Theorems.Thm_ActuarialValuation_presentValue_variance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Ω → ℝ) (hT : Measurable T)
    (hTnonneg : ∀ ω, 0 ≤ T ω) (v : ℝ) (n : ℕ)
    : ProbabilityTheory.variance (pureEndowmentPV T v n) P = (v ^ n) ^ 2 * (P (strictSurvivalEvent T n)).toReal * (1 - (P (strictSurvivalEvent T n)).toReal) := by
  classical
  let A : Set Ω := strictSurvivalEvent T n
  have hA : MeasurableSet A := by
    change MeasurableSet (T ⁻¹' Set.Ioi (n : ℝ))
    exact hT measurableSet_Ioi
  let payments : Finset ℕ := {0}
  let tm : ℕ → ℕ := fun _ => n
  let disc : ℕ → ℝ := fun _ => v ^ n
  let amt : ℕ → ℝ := fun _ => 1
  let trigger : ℕ → Set Ω := fun _ => A
  have hm : ∀ i ∈ payments, MeasurableSet (trigger i) := by
    intro i hi
    exact hA
  have heq : pureEndowmentPV T v n =
      presentValue payments tm disc amt trigger := by
    funext ω
    simp [pureEndowmentPV, presentValue, payments, tm, disc, amt, trigger, A]
  have hv := presentValue_variance P payments tm disc amt trigger hm
  calc
    ProbabilityTheory.variance (pureEndowmentPV T v n) P =
        ProbabilityTheory.variance (presentValue payments tm disc amt trigger) P := by rw [heq]
    _ = (v ^ n) ^ 2 * (P (strictSurvivalEvent T n)).toReal *
        (1 - (P (strictSurvivalEvent T n)).toReal) := by
      rw [hv]
      simp only [payments, tm, disc, amt, trigger, A, Finset.sum_singleton,
        Set.inter_self, mul_one]
      ring
