-- Prove2me | solution 1 for ActuarialValuation.negBinCountMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:47:48.196979+00:00
-- url     : https://prove2.me/submissions/902cac04-faed-48da-b024-b1c942371460

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinCountMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r n : ℕ) (p : ℝ)
  (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
  0 ≤ negBinCountMass r p n := by
  have hcomp : 0 ≤ 1 - p := by linarith
  unfold negBinCountMass
  positivity
