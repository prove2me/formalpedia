-- Prove2me | solution 1 for ActuarialValuation.termPolicyLoss_expected_linear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:09:31.849376+00:00
-- url     : https://prove2.me/submissions/0bd3cf73-5f36-450b-a106-54eb377f43c1

import Mathlib
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_premiumDuePV
import Definitions.Def_actuarial_termPolicyLossPV
import Theorems.Thm_ActuarialValuation_deathYearEvent_measurable
import Theorems.Thm_ActuarialValuation_presentValue_memLp_two
import Theorems.Thm_ActuarialValuation_premiumDuePV_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n : ℕ) (b π : ℝ)
    :
    (∫ ω, termPolicyLossPV K v n b π ω ∂P) =
      b * (∫ ω, termAssurancePV K v n ω ∂P) -
      π * (∫ ω, premiumDuePV K v n ω ∂P) := by
  have htrig : ∀ k ∈ Finset.range n,
      MeasurableSet (deathYearEvent K k) := by
    intro k hk
    exact deathYearEvent_measurable K hK k
  have hL2 : MemLp (termAssurancePV K v n) 2 P := by
    unfold termAssurancePV
    exact presentValue_memLp_two P (Finset.range n)
      (fun k : ℕ => k + 1) (fun t : ℕ => v ^ t)
      (fun _ : ℕ => (1 : ℝ)) (deathYearEvent K) htrig
  have hA : Integrable (termAssurancePV K v n) P :=
    hL2.integrable (by norm_num)
  have hY : Integrable (premiumDuePV K v n) P :=
    premiumDuePV_integrable P K hK v n
  change (∫ ω, b * termAssurancePV K v n ω -
      π * premiumDuePV K v n ω ∂P) = _
  rw [integral_sub (hA.const_mul b) (hY.const_mul π)]
  simp only [integral_const_mul]
