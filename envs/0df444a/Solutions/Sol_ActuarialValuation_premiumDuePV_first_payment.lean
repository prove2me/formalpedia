-- Prove2me | solution 1 for ActuarialValuation.premiumDuePV_first_payment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:51:17.441608+00:00
-- url     : https://prove2.me/submissions/a146cc3a-8835-4584-9b95-4ea08986aa24

import Mathlib
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_premiumDuePV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω)
    (hn : 0 < n) (hv : 0 ≤ v)
    : 1 ≤ premiumDuePV K v n ω := by
  have hzero : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.mpr hn
  have hnonneg (k : ℕ) : 0 ≤ (if k ≤ K ω then v ^ k else (0 : ℝ)) := by
    split_ifs <;> positivity
  have hle : (if (0 : ℕ) ≤ K ω then v ^ (0 : ℕ) else (0 : ℝ)) ≤
      ∑ k ∈ Finset.range n, (if k ≤ K ω then v ^ k else (0 : ℝ)) := by
    exact Finset.single_le_sum (fun k hk => hnonneg k) hzero
  simpa [premiumDuePV] using hle
