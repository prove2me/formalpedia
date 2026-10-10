-- Prove2me | solution 1 for ActuarialValuation.negBinGammaProbability_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:44:27.440436+00:00
-- url     : https://prove2.me/submissions/53e252ea-6d6a-4f86-9f54-469046ba992b

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
  negBinGammaProbability b < 1 := by
  change 1 / (b + 1) < 1
  have hden : 0 < b + 1 := by linarith
  rw [div_lt_iff₀ hden]
  nlinarith
