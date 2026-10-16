-- Prove2me | solution 1 for ActuarialAnnuitiesBridge.bridge_interest_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T05:59:49.379268+00:00
-- url     : https://prove2.me/submissions/dd237e17-b577-46bd-8bca-93c20ec4af8d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true


theorem solution (rho : ℝ) (j : ℕ) :
    (Real.exp (-rho))^j = Real.exp (-rho * (j : ℝ)) := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring
