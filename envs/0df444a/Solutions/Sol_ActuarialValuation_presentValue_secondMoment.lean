-- Prove2me | solution 1 for ActuarialValuation.presentValue_secondMoment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:17:43.603897+00:00
-- url     : https://prove2.me/submissions/a31837f5-0b9b-49d7-a243-e78c317fdb63

import Mathlib
import Definitions.Def_actuarial_presentValue
import Theorems.Thm_ActuarialValuation_jointPayment_expectation
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
    (∫ ω, (presentValue payments time discount amount trigger ω) ^ 2 ∂P =
      ∑ i ∈ payments, ∑ j ∈ payments,
        (discount (time i) * amount i) *
          (discount (time j) * amount j) *
          (P (trigger i ∩ trigger j)).toReal) := by
  classical
  let w : ι → ℝ := fun i => discount (time i) * amount i
  let ind : ι → Ω → ℝ :=
    fun i ω => (trigger i).indicator (fun _ : Ω => (1 : ℝ)) ω
  have hPV (ω : Ω) :
      presentValue payments time discount amount trigger ω =
        ∑ i ∈ payments, w i * ind i ω := rfl
  have hpair (i j : ι) :
      (fun ω : Ω => (w i * ind i ω) * (w j * ind j ω)) =
      (trigger i ∩ trigger j).indicator
        (fun _ : Ω => w i * w j) := by
    funext ω
    by_cases hi : ω ∈ trigger i <;> by_cases hj : ω ∈ trigger j <;>
      simp [ind, Set.indicator, hi, hj]
  have hpair_int (i j : ι) (hi : i ∈ payments) (hj : j ∈ payments) :
      Integrable
        (fun ω : Ω => (w i * ind i ω) * (w j * ind j ω)) P := by
    rw [hpair i j]
    exact (integrable_const (w i * w j)).indicator
      ((htrigger i hi).inter (htrigger j hj))
  have hpair_expectation (i j : ι) (hi : i ∈ payments)
      (hj : j ∈ payments) :
      (∫ ω, (w i * ind i ω) * (w j * ind j ω) ∂P) =
        w i * w j * (P (trigger i ∩ trigger j)).toReal := by
    calc
      (∫ ω, (w i * ind i ω) * (w j * ind j ω) ∂P) =
          (∫ ω, (w i * w j) * (ind i ω * ind j ω) ∂P) := by
        congr 1
        funext ω
        ring
      _ = (w i * w j) * (∫ ω, ind i ω * ind j ω ∂P) := by
        rw [integral_const_mul]
      _ = w i * w j * (P (trigger i ∩ trigger j)).toReal := by
        change (w i * w j) *
            (∫ ω, (trigger i).indicator (fun _ : Ω => (1 : ℝ)) ω *
                (trigger j).indicator (fun _ : Ω => (1 : ℝ)) ω ∂P) =
              w i * w j * (P (trigger i ∩ trigger j)).toReal
        rw [jointPayment_expectation P (trigger i) (trigger j)
          (htrigger i hi) (htrigger j hj)]
  have hexpand (ω : Ω) :
      (presentValue payments time discount amount trigger ω) ^ 2 =
        ∑ i ∈ payments, ∑ j ∈ payments,
          (w i * ind i ω) * (w j * ind j ω) := by
    rw [hPV]
    calc
      (∑ i ∈ payments, w i * ind i ω) ^ 2 =
          (∑ i ∈ payments, w i * ind i ω) *
            (∑ j ∈ payments, w j * ind j ω) := by ring
      _ = ∑ i ∈ payments, ∑ j ∈ payments,
            (w i * ind i ω) * (w j * ind j ω) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
  calc
    (∫ ω, (presentValue payments time discount amount trigger ω) ^ 2 ∂P) =
        (∫ ω, ∑ i ∈ payments, ∑ j ∈ payments,
          (w i * ind i ω) * (w j * ind j ω) ∂P) := by
          congr 1
          funext ω
          exact hexpand ω
    _ = ∑ i ∈ payments, ∑ j ∈ payments,
          (∫ ω, (w i * ind i ω) * (w j * ind j ω) ∂P) := by
      rw [MeasureTheory.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [MeasureTheory.integral_finset_sum]
        intro j hj
        exact hpair_int i j hi hj
      · intro i hi
        apply MeasureTheory.integrable_finset_sum
        intro j hj
        exact hpair_int i j hi hj
    _ = ∑ i ∈ payments, ∑ j ∈ payments,
          (discount (time i) * amount i) *
          (discount (time j) * amount j) *
          (P (trigger i ∩ trigger j)).toReal := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hpair_expectation i j hi hj
