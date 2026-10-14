-- Prove2me | solution 2 for ActuarialValuation.utPositiveStoploss_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:40.378105+00:00
-- url     : https://prove2.me/submissions/2ddedec2-6d51-4358-87d2-664d6374c0e8

import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_utPositiveStoploss

open ActuarialValuation

theorem solution (retention loss : ℝ) (h : loss≤retention) : utPositiveStoploss retention loss=0 := by simp [utPositiveStoploss, max_eq_left (sub_nonpos.mpr h)]

