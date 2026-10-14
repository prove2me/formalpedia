-- Prove2me | solution 1 for ActuarialValuation.nhCumulative_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:43:04.008391+00:00
-- url     : https://prove2.me/submissions/8f17cafe-dc2a-4690-bf97-6c1c890279f8

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhIntensity
import Definitions.Def_actuarial_nhCumulative

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b t : ℝ) : HasDerivAt (nhCumulative a b) (nhIntensity a b t) t := by
  unfold nhCumulative nhIntensity
  have h1 := (hasDerivAt_id t).const_mul a
  have h2 := ((hasDerivAt_id t).pow 2).const_mul (b/2)
  convert h1.add h2 using 1 <;>
    first
    | rfl
    | (funext x; dsimp; ring)
    | (norm_num [pow_one]; ring)
