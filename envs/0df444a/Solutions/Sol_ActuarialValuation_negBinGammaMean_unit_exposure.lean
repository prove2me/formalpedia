-- Prove2me | solution 1 for ActuarialValuation.negBinGammaMean_unit_exposure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:49:18.809242+00:00
-- url     : https://prove2.me/submissions/2d46554c-60c4-4ce9-a28a-05958600b9a0

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinCountMean
import Definitions.Def_actuarial_negBinGammaProbability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r : ℕ) (b : ℝ)
  (hb : 0 < b) :
  negBinCountMean r (negBinGammaProbability b) = (r : ℝ) / b := by
  unfold negBinCountMean negBinGammaProbability
  field_simp [ne_of_gt hb, ne_of_gt (show 0 < b + 1 by linarith)]
  <;> ring
