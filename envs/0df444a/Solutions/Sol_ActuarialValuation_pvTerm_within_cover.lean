-- Prove2me | solution 1 for ActuarialValuation.pvTerm_within_cover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:55:04.418984+00:00
-- url     : https://prove2.me/submissions/df7256dd-436f-4713-9e6c-289933fb414b

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvTermBenefit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (benefit discount : ℕ → ℝ) (term k : ℕ) (h : k < term) : pvTermBenefit benefit discount term k = benefit k * discount (k+1) := by
  simp [pvTermBenefit, h]
