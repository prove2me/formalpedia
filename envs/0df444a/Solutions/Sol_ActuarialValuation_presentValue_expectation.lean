-- Prove2me | solution 1 for ActuarialValuation.presentValue_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:17:34.613907+00:00
-- url     : https://prove2.me/submissions/a5bed0ec-4ac4-44e6-ab98-55a8d28f0cc3

import Mathlib
import Definitions.Def_actuarial_presentValue
import Theorems.Thm_ActuarialValuation_singlePayment_expectation
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
    (∫ ω, presentValue payments time discount amount trigger ω ∂P =
      ∑ i ∈ payments, discount (time i) * amount i *
        (P (trigger i)).toReal) := by
  classical
  unfold presentValue
  have hterm (i : ι) (hi : i ∈ payments) :
      Integrable
        (fun ω : Ω => discount (time i) * amount i *
          (trigger i).indicator (fun _ : Ω => (1 : ℝ)) ω) P := by
    have hc :
        Integrable ((trigger i).indicator
          (fun _ : Ω => discount (time i) * amount i)) P :=
      (integrable_const (discount (time i) * amount i)).indicator (htrigger i hi)
    convert hc using 1
    funext ω
    by_cases hw : ω ∈ trigger i
    · simp [Set.indicator, hw]
    · simp [Set.indicator, hw]
  rw [MeasureTheory.integral_finset_sum payments hterm]
  apply Finset.sum_congr rfl
  intro i hi
  exact singlePayment_expectation P (trigger i) (htrigger i hi)
    (discount (time i)) (amount i)
