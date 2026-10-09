-- Prove2me | solution 1 for ActuarialValuation.temporaryAnnuityDue_variance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:34:55.995982+00:00
-- url     : https://prove2.me/submissions/ac0f938f-6886-47b6-8c79-422c1a4822f2

import Mathlib
import Definitions.Def_actuarial_temporaryAnnuityDuePV
import Theorems.Thm_ActuarialValuation_presentValue_memLp_two
import Theorems.Thm_ActuarialValuation_presentValue_secondMoment
import Theorems.Thm_ActuarialValuation_temporaryAnnuityDue_expectation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation
open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K) (v : ℝ) (n : ℕ)
    :
    ProbabilityTheory.variance (temporaryAnnuityDuePV K v n) P = (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (v ^ i) * (v ^ j) * (P (curtateSurvivalEvent K (max i j))).toReal) - (∑ k ∈ Finset.range n, v ^ k * (P (curtateSurvivalEvent K k)).toReal) ^ 2 := by
  classical
  have htrigger :
      ∀ k ∈ Finset.range n, MeasurableSet (curtateSurvivalEvent K k) := by
    intro k hk
    change MeasurableSet (K ⁻¹' Set.Ici k)
    exact hK measurableSet_Ici
  have hL2 : MemLp (temporaryAnnuityDuePV K v n) 2 P := by
    unfold temporaryAnnuityDuePV
    exact presentValue_memLp_two P (Finset.range n)
      (fun k : ℕ => k) (fun t : ℕ => v ^ t)
      (fun _ : ℕ => (1 : ℝ)) (curtateSurvivalEvent K) htrigger
  have hinter : ∀ (a b : ℕ),
      curtateSurvivalEvent K a ∩ curtateSurvivalEvent K b =
      curtateSurvivalEvent K (max a b) := by
    intro a b
    ext ω
    change (a ≤ K ω ∧ b ≤ K ω) ↔ max a b ≤ K ω
    exact max_le_iff.symm
  have hsecond :
      (∫ ω, (temporaryAnnuityDuePV K v n ω) ^ 2 ∂P) =
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        (v ^ i) * (v ^ j) *
        (P (curtateSurvivalEvent K (max i j))).toReal := by
    unfold temporaryAnnuityDuePV
    simpa only [mul_one, hinter] using
      (presentValue_secondMoment P (Finset.range n)
        (fun k : ℕ => k) (fun t : ℕ => v ^ t)
        (fun _ : ℕ => (1 : ℝ)) (curtateSurvivalEvent K) htrigger)
  rw [ProbabilityTheory.variance_eq_sub hL2]
  simp only [Pi.pow_apply]
  rw [hsecond, temporaryAnnuityDue_expectation P K hK v n]
