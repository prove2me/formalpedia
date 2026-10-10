-- Prove2me | solution 1 for ActuarialValuation.negBinCountMass_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:47:12.721616+00:00
-- url     : https://prove2.me/submissions/86ff4371-b9c4-4702-badf-26666fb2cc00

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinCountMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r : ℕ) (p : ℝ) (hr : 0 < r) :
  negBinCountMass r p 0 = (1 - p) ^ r := by
  simp [negBinCountMass]
