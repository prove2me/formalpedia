-- Prove2me | solution 1 for ActuarialValuation.tailRiskAtomWeight_le_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:39:32.651853+00:00
-- url     : https://prove2.me/submissions/e9d75e1b-b1ba-441f-b6bb-de9c663b67f5

import Mathlib.Tactic.Linarith
import Definitions.Def_actuarial_tailRiskAtomWeight
import Definitions.Def_actuarial_tailRiskStrictMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (bound q : ℕ) (alpha : ℝ)
  (hquantile : 1 - alpha ≤ tailRiskStrictMass w bound q + w q) :
  tailRiskAtomWeight w bound q alpha ≤ w q := by
  unfold tailRiskAtomWeight
  linarith
