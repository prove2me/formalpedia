-- Prove2me | solution 1 for ActuarialValuation.trancheSchemePension_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:04:39.910734+00:00
-- url     : https://prove2.me/submissions/12664750-6857-4bca-9c99-24f1e920a453

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_trancheSchemePension
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (P A D : ℕ → ℝ) :
  trancheSchemePension P A D 0 = 0 := by
  simp [trancheSchemePension]
