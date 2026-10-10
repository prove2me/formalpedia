-- Prove2me | solution 1 for ActuarialValuation.tailRiskAtomWeight_coverage
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:37:04.238975+00:00
-- url     : https://prove2.me/submissions/e675b295-5da2-4c85-ba7b-1e9bf189b439

import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_tailRiskAtomWeight
import Definitions.Def_actuarial_tailRiskStrictMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (bound q : ℕ) (alpha : ℝ) :
  tailRiskStrictMass w bound q + tailRiskAtomWeight w bound q alpha =
    1 - alpha := by
  unfold tailRiskAtomWeight
  ring
