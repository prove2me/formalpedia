-- Prove2me | solution 1 for ActuarialValuation.negBinGammaProbability_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:45:46.702063+00:00
-- url     : https://prove2.me/submissions/511e5745-7991-4fb4-960d-fbbd62c3c6d5

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinGammaProbability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (b : ℝ) (hb : 0 < b) :
  0 < negBinGammaProbability b := by
  change 0 < 1 / (b + 1)
  exact div_pos zero_lt_one (by linarith)
