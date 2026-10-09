-- Prove2me | solution 1 for ActuarialValuation.presentValue_memLp_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:14:08.74111+00:00
-- url     : https://prove2.me/submissions/98af0bc1-101a-41d1-a41c-d29f8168e117

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
    MemLp (presentValue payments time discount amount trigger) 2 P := by
  classical
  unfold presentValue
  apply MeasureTheory.memLp_finset_sum
  intro i hi
  have hc : MemLp (fun _ : Ω => (1 : ℝ)) 2 P :=
    MeasureTheory.memLp_const (μ := P) (p := 2) (1 : ℝ)
  have hiLp :
      MemLp ((trigger i).indicator (fun _ : Ω => (1 : ℝ))) 2 P :=
    hc.indicator (htrigger i hi)
  exact hiLp.const_mul (discount (time i) * amount i)
