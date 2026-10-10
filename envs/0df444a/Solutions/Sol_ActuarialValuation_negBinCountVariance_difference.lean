-- Prove2me | solution 1 for ActuarialValuation.negBinCountVariance_difference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:10:21.52232+00:00
-- url     : https://prove2.me/submissions/8cdfca63-0ca1-4da8-a318-cee6742c6aa5

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinCountMean
import Definitions.Def_actuarial_negBinCountVariance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r : ℕ) (p : ℝ)
  (hp : p ≠ 1) :
  negBinCountVariance r p - negBinCountMean r p =
    (r : ℝ) * p ^ 2 / (1 - p) ^ 2 := by
  unfold negBinCountVariance negBinCountMean
  have hden : 1 - p ≠ 0 := by
    intro h
    apply hp
    linarith
  field_simp [hden]
  ring
