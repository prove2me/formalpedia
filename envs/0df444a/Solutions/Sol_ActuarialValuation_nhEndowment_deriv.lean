-- Prove2me | solution 1 for ActuarialValuation.nhEndowment_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:06:49.940858+00:00
-- url     : https://prove2.me/submissions/2954d3a8-69d8-4707-a542-78867a1dcb5e

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhIntensity
import Definitions.Def_actuarial_nhEndowment

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b δ T B t : ℝ) : HasDerivAt (nhEndowment a b δ T B) ((δ+nhIntensity a b t)*nhEndowment a b δ T B t) t := by
  have hcum : HasDerivAt (nhCumulative a b) (nhIntensity a b t) t := by
    unfold nhCumulative nhIntensity
    have h1 := (hasDerivAt_id t).const_mul a
    have h2 := ((hasDerivAt_id t).pow 2).const_mul (b/2)
    convert h1.add h2 using 1 <;>
      first
      | rfl
      | (funext x; dsimp; ring)
      | (norm_num [pow_one]; ring)
  have hinner : HasDerivAt
      (fun x : ℝ => δ*x + nhCumulative a b x -
        (δ*T + nhCumulative a b T))
      (δ + nhIntensity a b t) t := by
    convert (((hasDerivAt_id t).const_mul δ).add hcum).sub_const
      (δ*T + nhCumulative a b T) using 1 <;>
      first
      | rfl
      | (funext x; dsimp; ring)
      | ring
  have hE (x : ℝ) :
      nhEndowment a b δ T B x =
        B * Real.exp (δ*x + nhCumulative a b x -
          (δ*T + nhCumulative a b T)) := by
    unfold nhEndowment nhSurvival
    rw [show δ*x + nhCumulative a b x -
        (δ*T + nhCumulative a b T) =
        -δ*(T-x) + -(nhCumulative a b T - nhCumulative a b x)
        by ring, Real.exp_add]
    ring
  have hder :=
    ((Real.hasDerivAt_exp _).comp t hinner).const_mul B
  have heq : (nhEndowment a b δ T B) =
      (fun x => B * Real.exp (δ*x + nhCumulative a b x -
        (δ*T + nhCumulative a b T))) := funext hE
  rw [heq]
  convert hder using 1 <;>
    first
    | rfl
    | ring
