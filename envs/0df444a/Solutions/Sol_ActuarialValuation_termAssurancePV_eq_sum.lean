-- Prove2me | solution 1 for ActuarialValuation.termAssurancePV_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T19:21:03.004064+00:00
-- url     : https://prove2.me/submissions/ee2f9a91-211c-4704-9c48-9f961b0da571

import Mathlib
import Definitions.Def_actuarial_deathYearEvent
import Definitions.Def_actuarial_termAssurancePV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation
open MeasureTheory

theorem solution {Ω : Type*}
    (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω)
    :
    termAssurancePV K v n ω =
      ∑ k ∈ Finset.range n, v ^ (k + 1) *
        (deathYearEvent K k).indicator (fun _ : Ω => (1 : ℝ)) ω := by
  simp [termAssurancePV, presentValue]
