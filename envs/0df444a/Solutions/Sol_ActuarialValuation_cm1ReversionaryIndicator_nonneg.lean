-- Prove2me | solution 1 for ActuarialValuation.cm1ReversionaryIndicator_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:16:57.887751+00:00
-- url     : https://prove2.me/submissions/ca3cdd7d-669b-4d78-90f4-81c30f2c30bd

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1ReversionaryIndicator
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (pY both : ℕ → ℝ) (t : ℕ) (h : both t ≤ pY t) : 0 ≤ cm1ReversionaryIndicator pY both t := by
  unfold cm1ReversionaryIndicator
  exact sub_nonneg.mpr h
