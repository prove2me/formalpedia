-- Prove2me | solution 1 for ActuarialValuation.termAssurance_secondMoment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T19:22:51.283241+00:00
-- url     : https://prove2.me/submissions/b6442fc2-e2d7-4c39-8fd1-a8964947a30c

import Mathlib
import Definitions.Def_actuarial_deathYearEvent
import Definitions.Def_actuarial_termAssurancePV
import Theorems.Thm_ActuarialValuation_presentValue_secondMoment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n : ℕ)
    :
    (∫ ω, (termAssurancePV K v n ω) ^ 2 ∂P) =
      ∑ k ∈ Finset.range n, (v ^ (k + 1)) ^ 2 * (P (deathYearEvent K k)).toReal := by
  classical
  have htrigger :
      ∀ k ∈ Finset.range n, MeasurableSet (deathYearEvent K k) := by
    intro k hk
    change MeasurableSet (K ⁻¹' ({k} : Set ℕ))
    exact hK (measurableSet_singleton k)
  have hbase :=
    presentValue_secondMoment P (Finset.range n)
      (fun k : ℕ => k + 1) (fun t : ℕ => v ^ t)
      (fun _ : ℕ => (1 : ℝ)) (deathYearEvent K) htrigger
  unfold termAssurancePV
  simp only [mul_one] at hbase
  rw [hbase]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · simp [pow_two]
  · intro j hj hji
    have hdistinct : i ≠ j := by
      intro heq
      exact hji heq.symm
    have hdisj :
        Disjoint (deathYearEvent K i) (deathYearEvent K j) :=
      by
        apply Set.disjoint_left.mpr
        intro ω hi' hj'
        have heqi : K ω = i := hi'
        have heqj : K ω = j := hj'
        exact hdistinct (heqi.symm.trans heqj)
    have hempty :
        deathYearEvent K i ∩ deathYearEvent K j = ∅ :=
      Set.disjoint_iff_inter_eq_empty.mp hdisj
    simp [hempty]
  · intro hiNot
    exact False.elim (hiNot hi)
