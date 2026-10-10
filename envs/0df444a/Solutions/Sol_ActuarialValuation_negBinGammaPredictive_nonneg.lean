-- Prove2me | solution 1 for ActuarialValuation.negBinGammaPredictive_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:48:32.624999+00:00
-- url     : https://prove2.me/submissions/00c37b8c-6341-449c-8ab1-c01294e80cee

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinGammaPredictive
import Definitions.Def_actuarial_negBinGammaProbability
import Definitions.Def_actuarial_negBinCountMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r n : ℕ) (b : ℝ)
  (hb : 0 < b) :
  0 ≤ negBinGammaPredictive r b n := by
  have hden : 0 < b + 1 := by linarith
  have hp : 0 ≤ 1 / (b + 1) := div_nonneg (by norm_num) (le_of_lt hden)
  have hcomp : 0 ≤ 1 - 1 / (b + 1) := by
    apply sub_nonneg.mpr
    rw [div_le_iff₀ hden]
    nlinarith
  unfold negBinGammaPredictive negBinGammaProbability negBinCountMass
  positivity
