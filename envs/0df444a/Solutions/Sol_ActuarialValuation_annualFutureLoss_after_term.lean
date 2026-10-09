-- Prove2me | solution 1 for ActuarialValuation.annualFutureLoss_after_term
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:18:07.549511+00:00
-- url     : https://prove2.me/submissions/652023c2-41b2-46f4-8b69-bfc673d7bad3

import Mathlib
import Definitions.Def_actuarial_annualFutureLoss
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n t : ℕ) (b π : ℝ) (ω : Ω) (ht : n ≤ t)
  : annualFutureLoss K v n t b π ω = 0 := by
  have hb : ¬ (t ≤ K ω ∧ K ω < n) := by omega
  have hs : (∑ j ∈ Finset.range n,
      if t ≤ j ∧ j ≤ K ω then v ^ (j - t) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjlt := Finset.mem_range.mp hj
    have hnot : ¬t ≤ j := by omega
    simp [hnot]
  simp [annualFutureLoss, hb, hs]
