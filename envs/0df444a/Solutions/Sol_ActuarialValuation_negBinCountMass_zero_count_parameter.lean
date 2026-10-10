-- Prove2me | solution 1 for ActuarialValuation.negBinCountMass_zero_count_parameter
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:46:33.124333+00:00
-- url     : https://prove2.me/submissions/4cca92be-76c8-4de0-a801-3f1c9a1652a2

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinCountMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r n : ℕ) (hn : 0 < n) :
  negBinCountMass r 0 n = 0 := by
  simp [negBinCountMass, Nat.ne_of_gt hn]
