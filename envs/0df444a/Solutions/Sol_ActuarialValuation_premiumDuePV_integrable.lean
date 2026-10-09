-- Prove2me | solution 1 for ActuarialValuation.premiumDuePV_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:02:00.19364+00:00
-- url     : https://prove2.me/submissions/3c41c683-bc24-485b-926c-43c285ad9a16

import Mathlib
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_premiumDuePV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n : ℕ)
    : Integrable (premiumDuePV K v n) P := by
  classical
  have hterm (k : ℕ) :
      Integrable (fun ω : Ω => if k ≤ K ω then v ^ k else 0) P := by
    have hs : MeasurableSet {ω : Ω | k ≤ K ω} := by
      change MeasurableSet (K ⁻¹' Set.Ici k)
      exact hK measurableSet_Ici
    have hc : Integrable (fun _ : Ω => (v ^ k : ℝ)) P := integrable_const _
    have hfun :
        (fun ω : Ω => if k ≤ K ω then v ^ k else (0 : ℝ)) =
        {ω : Ω | k ≤ K ω}.indicator (fun _ : Ω => v ^ k) := by
      funext ω
      by_cases hk : k ≤ K ω <;> simp [Set.indicator, hk]
    rw [hfun]
    exact hc.indicator hs
  change Integrable (fun ω : Ω =>
    ∑ k ∈ Finset.range n, (if k ≤ K ω then v ^ k else 0)) P
  exact integrable_finset_sum (Finset.range n) (fun k hk => hterm k)
