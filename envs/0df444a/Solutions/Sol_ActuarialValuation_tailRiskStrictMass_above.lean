-- Prove2me | solution 1 for ActuarialValuation.tailRiskStrictMass_above
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:40:38.948637+00:00
-- url     : https://prove2.me/submissions/032fb1ca-da12-4f69-85ce-a4a291453f0b

import Mathlib
import Definitions.Def_actuarial_tailRiskStrictMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (bound q : ℕ) (h : bound ≤ q) :
  tailRiskStrictMass w bound q = 0 := by
  unfold tailRiskStrictMass
  apply Finset.sum_eq_zero
  intro s hs
  have hsle : s ≤ bound := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  have hfalse : ¬ q < s := by omega
  simp [hfalse]
