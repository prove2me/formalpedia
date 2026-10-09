-- Prove2me | solution 2 for ActuarialValuation.annualFutureLoss_after_term
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:18:42.40233+00:00
-- url     : https://prove2.me/submissions/0158f831-af48-42f0-90e5-bea3ef9c2214

import Mathlib
import Definitions.Def_actuarial_annualFutureLoss
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} (K : Ω → ℕ) (v : ℝ)
    (n t : ℕ) (b π : ℝ) (ω : Ω) (ht : n ≤ t) :
    annualFutureLoss K v n t b π ω = 0 := by
  have hclaim : ¬ (t ≤ K ω ∧ K ω < n) := by omega
  have hsum : (∑ j ∈ Finset.range n,
      if t ≤ j ∧ j ≤ K ω then v ^ (j - t) else (0 : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    have hfalse : ¬ (t ≤ j ∧ j ≤ K ω) := by omega
    simp [hfalse]
  simp [annualFutureLoss, hclaim, hsum]
