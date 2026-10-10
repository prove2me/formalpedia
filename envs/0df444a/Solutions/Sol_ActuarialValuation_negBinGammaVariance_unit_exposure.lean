-- Prove2me | solution 1 for ActuarialValuation.negBinGammaVariance_unit_exposure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:50:24.985998+00:00
-- url     : https://prove2.me/submissions/225d9f14-f280-49a2-a626-5f7b54f7ee7d

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinCountVariance
import Definitions.Def_actuarial_negBinGammaProbability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r : ℕ) (b : ℝ)
  (hb : 0 < b) :
  negBinCountVariance r (negBinGammaProbability b) =
    (r : ℝ) / b + (r : ℝ) / b ^ 2 := by
  unfold negBinCountVariance negBinGammaProbability
  field_simp [ne_of_gt hb, ne_of_gt (show 0 < b + 1 by linarith)]
  <;> ring
