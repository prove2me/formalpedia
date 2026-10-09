-- Prove2me | solution 1 for ActuarialValuation.presentValue_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:08:16.786294+00:00
-- url     : https://prove2.me/submissions/1d5a8197-4526-4234-91cb-403815717403

import Mathlib
import Definitions.Def_actuarial_presentValue
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
    Integrable (presentValue payments time discount amount trigger) P := by
  classical
  unfold presentValue
  apply MeasureTheory.integrable_finset_sum
  intro i hi
  have hterm :
      Integrable ((trigger i).indicator
        (fun _ : Ω => discount (time i) * amount i)) P :=
    (integrable_const (discount (time i) * amount i)).indicator (htrigger i hi)
  have hfun :
      (fun ω : Ω => discount (time i) * amount i *
        (trigger i).indicator (fun _ : Ω => (1 : ℝ)) ω) =
      (trigger i).indicator
        (fun _ : Ω => discount (time i) * amount i) := by
    funext ω
    by_cases hω : ω ∈ trigger i
    · simp [Set.indicator, hω]
    · simp [Set.indicator, hω]
  rw [hfun]
  exact hterm
