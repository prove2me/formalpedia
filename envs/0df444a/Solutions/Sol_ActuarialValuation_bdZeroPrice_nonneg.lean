-- Prove2me | solution 1 for ActuarialValuation.bdZeroPrice_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:55:55.371475+00:00
-- url     : https://prove2.me/submissions/facbdf55-35c9-4486-abca-0002ecc0127c

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdZeroPrice

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (D : ℕ → ℝ) (face : ℝ) (t : ℕ) (hf : 0≤face) (hD : 0≤D t) : 0≤bdZeroPrice D face t := by
  unfold bdZeroPrice
  exact mul_nonneg hf hD
