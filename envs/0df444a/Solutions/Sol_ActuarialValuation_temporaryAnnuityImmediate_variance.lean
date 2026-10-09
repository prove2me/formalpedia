-- Prove2me | solution 1 for ActuarialValuation.temporaryAnnuityImmediate_variance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:34:56.069455+00:00
-- url     : https://prove2.me/submissions/dd01c818-3f1b-45fa-8715-ce5395985f8b

import Mathlib
import Definitions.Def_actuarial_temporaryAnnuityImmediatePV
import Theorems.Thm_ActuarialValuation_presentValue_memLp_two
import Theorems.Thm_ActuarialValuation_presentValue_secondMoment
import Theorems.Thm_ActuarialValuation_temporaryAnnuityImmediate_expectation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation
open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K) (v : ℝ) (n : ℕ)
    :
    ProbabilityTheory.variance (temporaryAnnuityImmediatePV K v n) P = (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (v ^ (i + 1)) * (v ^ (j + 1)) * (P (curtateSurvivalEvent K (max (i + 1) (j + 1)))).toReal) - (∑ k ∈ Finset.range n, v ^ (k + 1) * (P (curtateSurvivalEvent K (k + 1))).toReal) ^ 2 := by
  classical
  have htrigger :
      ∀ k ∈ Finset.range n, MeasurableSet (curtateSurvivalEvent K (k + 1)) := by
    intro k hk
    change MeasurableSet (K ⁻¹' Set.Ici (k + 1))
    exact hK measurableSet_Ici
  have hL2 : MemLp (temporaryAnnuityImmediatePV K v n) 2 P := by
    unfold temporaryAnnuityImmediatePV
    exact presentValue_memLp_two P (Finset.range n)
      (fun k : ℕ => k + 1) (fun t : ℕ => v ^ t)
      (fun _ : ℕ => (1 : ℝ))
      (fun k : ℕ => curtateSurvivalEvent K (k + 1)) htrigger
  have hinter : ∀ (a b : ℕ),
      curtateSurvivalEvent K a ∩ curtateSurvivalEvent K b =
      curtateSurvivalEvent K (max a b) := by
    intro a b
    ext ω
    change (a ≤ K ω ∧ b ≤ K ω) ↔ max a b ≤ K ω
    exact max_le_iff.symm
  have hsecond :
      (∫ ω, (temporaryAnnuityImmediatePV K v n ω) ^ 2 ∂P) =
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        (v ^ (i + 1)) * (v ^ (j + 1)) *
        (P (curtateSurvivalEvent K (max (i + 1) (j + 1)))).toReal := by
    unfold temporaryAnnuityImmediatePV
    simpa only [mul_one, hinter] using
      (presentValue_secondMoment P (Finset.range n)
        (fun k : ℕ => k + 1) (fun t : ℕ => v ^ t)
        (fun _ : ℕ => (1 : ℝ))
        (fun k : ℕ => curtateSurvivalEvent K (k + 1)) htrigger)
  rw [ProbabilityTheory.variance_eq_sub hL2]
  simp only [Pi.pow_apply]
  rw [hsecond, temporaryAnnuityImmediate_expectation P K hK v n]
