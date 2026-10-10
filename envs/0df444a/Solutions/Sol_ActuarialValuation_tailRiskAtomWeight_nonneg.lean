-- Prove2me | solution 1 for ActuarialValuation.tailRiskAtomWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:39:24.845563+00:00
-- url     : https://prove2.me/submissions/cc4b58ef-c941-48b0-84dd-2ac1f3982dcf

import Mathlib.Tactic.Linarith
import Definitions.Def_actuarial_tailRiskAtomWeight
import Definitions.Def_actuarial_tailRiskStrictMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (bound q : ℕ) (alpha : ℝ)
  (htail : tailRiskStrictMass w bound q ≤ 1 - alpha) :
  0 ≤ tailRiskAtomWeight w bound q alpha := by
  unfold tailRiskAtomWeight
  linarith
