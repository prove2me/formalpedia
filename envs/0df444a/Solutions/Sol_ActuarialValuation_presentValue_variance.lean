-- Prove2me | solution 1 for ActuarialValuation.presentValue_variance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:18:18.13484+00:00
-- url     : https://prove2.me/submissions/adb50751-e9dd-4421-9fc0-16b6efc8e564

import Mathlib
import Definitions.Def_actuarial_presentValue
import Theorems.Thm_ActuarialValuation_presentValue_memLp_two
import Theorems.Thm_ActuarialValuation_presentValue_expectation
import Theorems.Thm_ActuarialValuation_presentValue_secondMoment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation
open MeasureTheory

/-- Proof template from a successful private Prove2Me compiler preflight.
Publication-time imports and the 'theorem solution' wrapper are not yet verified. -/
theorem solution {ι Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (payments : Finset ι) (time : ι → ℕ)
    (discount : ℕ → ℝ) (amount : ι → ℝ)
    (trigger : ι → Set Ω)
    (htrigger : ∀ i ∈ payments, MeasurableSet (trigger i)) :
    (ProbabilityTheory.variance
      (presentValue payments time discount amount trigger) P =
      ∑ i ∈ payments, ∑ j ∈ payments,
        (discount (time i) * amount i) *
          (discount (time j) * amount j) *
          ((P (trigger i ∩ trigger j)).toReal -
            (P (trigger i)).toReal * (P (trigger j)).toReal)) := by
  classical
  have hLp := presentValue_memLp_two P payments time discount amount trigger htrigger
  have hFirst := presentValue_expectation P payments time discount amount trigger htrigger
  have hSecond := presentValue_secondMoment P payments time discount amount trigger htrigger
  rw [ProbabilityTheory.variance_eq_sub hLp]
  change (∫ ω, (presentValue payments time discount amount trigger ω) ^ 2 ∂P) -
      (∫ ω, presentValue payments time discount amount trigger ω ∂P) ^ 2 = _
  rw [hSecond, hFirst]
  let w : ι → ℝ := fun i => discount (time i) * amount i
  let p : ι → ℝ := fun i => (P (trigger i)).toReal
  let q : ι → ι → ℝ := fun i j => (P (trigger i ∩ trigger j)).toReal
  change
    (∑ i ∈ payments, ∑ j ∈ payments, w i * w j * q i j) -
        (∑ i ∈ payments, w i * p i) ^ 2 =
      ∑ i ∈ payments, ∑ j ∈ payments,
        w i * w j * (q i j - p i * p j)
  have hsquare :
      (∑ i ∈ payments, w i * p i) ^ 2 =
        ∑ i ∈ payments, ∑ j ∈ payments,
          (w i * p i) * (w j * p j) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  rw [hsquare, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring
