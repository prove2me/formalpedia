-- Prove2me | solution 1 for ActuarialValuation.cm1SelectUltimateRate_zero_select
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:25:23.273842+00:00
-- url     : https://prove2.me/submissions/f95c66fd-900f-4307-97ac-ef94d8f69799

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1SelectUltimateRate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (select : ℕ → ℕ → ℝ) (ultimate : ℕ → ℝ) (x t : ℕ) : cm1SelectUltimateRate select ultimate x 0 t = ultimate (x+t) := by
  simp [cm1SelectUltimateRate]
