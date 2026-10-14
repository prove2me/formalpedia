-- Prove2me | solution 1 for ActuarialValuation.nhTransition_causeone_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:53:43.20883+00:00
-- url     : https://prove2.me/submissions/a65a4a8e-71b4-4ac9-a777-adde58a3ff6d

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhIntensity
import Definitions.Def_actuarial_nhSurvival
import Definitions.Def_actuarial_nhTransition

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

theorem solution (a b p s t : ℝ) : HasDerivAt (fun x => nhTransition a b p s x 0 1) (p*nhIntensity a b t*nhSurvival a b s t) t := by
  have hcum : HasDerivAt (nhCumulative a b) (nhIntensity a b t) t := by
    unfold nhCumulative nhIntensity
    have h1 := (hasDerivAt_id t).const_mul a
    have h2 := ((hasDerivAt_id t).pow 2).const_mul (b/2)
    convert h1.add h2 using 1 <;>
      first
      | rfl
      | (funext x; dsimp; ring)
      | (norm_num [pow_one]; ring)
  have hneg : HasDerivAt
      (fun x : ℝ => -(nhCumulative a b x - nhCumulative a b s))
      (-nhIntensity a b t) t := by
    convert (hcum.sub_const (nhCumulative a b s)).neg using 1 <;>
      first
      | rfl
      | (funext x; dsimp; ring)
      | ring
  have hexp := (Real.hasDerivAt_exp _).comp t hneg
  have hlive : HasDerivAt
      (fun x => nhTransition a b p s x 0 0)
      (-nhIntensity a b t*nhSurvival a b s t) t := by
    convert hexp using 1 <;>
      first
      | rfl
      | (funext x; dsimp [nhTransition, nhSurvival]; ring)
      | (simp [nhTransition, nhSurvival]; ring)
  have hsurv : HasDerivAt
      (fun x => nhSurvival a b s x)
      (-nhIntensity a b t*nhSurvival a b s t) t := by
    simpa [nhTransition] using hlive
  have hcompl : HasDerivAt
      (fun x => (1 : ℝ) - nhSurvival a b s x)
      (nhIntensity a b t*nhSurvival a b s t) t := by
    convert (hasDerivAt_const t (1 : ℝ)).sub hsurv using 1 <;>
      first
      | rfl
      | (funext x; dsimp; ring)
      | ring
  convert hcompl.const_mul p using 1 <;>
    first
    | rfl
    | (funext x; dsimp [nhTransition, nhExitOne]; ring)
    | ring
