-- Prove2me | solution 1 for ActuarialValuation.cm1LifeDecrement_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:20:44.786996+00:00
-- url     : https://prove2.me/submissions/0a3caccc-64de-4f2b-aca6-7c8a081e5c7e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1LifeDecrement
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (x n : ℕ) (hle : l (x+n+1) ≤ l (x+n)) : 0 ≤ cm1LifeDecrement l x n := by
  unfold cm1LifeDecrement
  exact sub_nonneg.mpr hle
