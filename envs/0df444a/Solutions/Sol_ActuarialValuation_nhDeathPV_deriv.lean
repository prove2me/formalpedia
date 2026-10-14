-- Prove2me | solution 1 for ActuarialValuation.nhDeathPV_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:12:54.937137+00:00
-- url     : https://prove2.me/submissions/bc2677d8-b078-4ed8-8d6c-a240c4e281ec

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhIntensity
import Definitions.Def_actuarial_nhCauseBenefit
import Definitions.Def_actuarial_nhDeathPV

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation MeasureTheory Filter
open scoped Topology

theorem solution (a b p δ B1 B2 T t : ℝ) : HasDerivAt (nhDeathPV a b p δ B1 B2 T) ((δ+nhIntensity a b t)*nhDeathPV a b p δ B1 B2 T t-nhIntensity a b t*nhCauseBenefit p B1 B2) t := by
  let g : ℝ → ℝ := fun x =>
    Real.exp (-δ*x - nhCumulative a b x) *
      nhIntensity a b x * nhCauseBenefit p B1 B2
  let A : ℝ → ℝ := fun z => Real.exp (δ*z + nhCumulative a b z)
  have hGcont : Continuous g := by
    dsimp [g, nhCumulative, nhIntensity, nhCauseBenefit]
    fun_prop
  have hInt : IntervalIntegrable g volume t T :=
    hGcont.intervalIntegrable t T
  have hMeas : StronglyMeasurableAtFilter g (𝓝 t) volume :=
    hGcont.stronglyMeasurableAtFilter volume (𝓝 t)
  have hI : HasDerivAt (fun z => ∫ x in z..T, g x) (-g t) t :=
    intervalIntegral.integral_hasDerivAt_left hInt hMeas hGcont.continuousAt
  have hC : HasDerivAt (nhCumulative a b) (nhIntensity a b t) t := by
    unfold nhCumulative nhIntensity
    have h1 := (hasDerivAt_id t).const_mul a
    have h2 := ((hasDerivAt_id t).pow 2).const_mul (b/2)
    convert h1.add h2 using 1 <;>
      first
      | rfl
      | (funext x; dsimp; ring)
      | (norm_num [pow_one]; ring)
  have hinner : HasDerivAt (fun z => δ*z + nhCumulative a b z)
      (δ + nhIntensity a b t) t := by
    convert ((hasDerivAt_id t).const_mul δ).add hC using 1 <;>
      first
      | rfl
      | (funext z; dsimp; ring)
      | ring
  have hA : HasDerivAt A ((δ + nhIntensity a b t)*A t) t := by
    dsimp [A]
    convert (Real.hasDerivAt_exp _).comp t hinner using 1 <;>
      first
      | rfl
      | (funext z; dsimp; ring)
      | ring
  have hzeroexp :
      Real.exp (δ*t + nhCumulative a b t) *
        Real.exp (-δ*t - nhCumulative a b t) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  have hcancel : A t * g t =
      nhIntensity a b t * nhCauseBenefit p B1 B2 := by
    dsimp [A,g]
    calc
      Real.exp (δ*t + nhCumulative a b t) *
          (Real.exp (-δ*t - nhCumulative a b t) *
            nhIntensity a b t * nhCauseBenefit p B1 B2) =
          (Real.exp (δ*t + nhCumulative a b t) *
            Real.exp (-δ*t - nhCumulative a b t)) *
            (nhIntensity a b t * nhCauseBenefit p B1 B2) := by ring
      _ = 1 * (nhIntensity a b t * nhCauseBenefit p B1 B2) := by
        rw [hzeroexp]
      _ = _ := by ring
  have hfact (z : ℝ) :
      nhDeathPV a b p δ B1 B2 T z = A z * (∫ x in z..T, g x) := by
    unfold nhDeathPV
    calc
      (∫ x in z..T, Real.exp (-δ*(x-z)) *
        nhSurvival a b z x * nhIntensity a b x *
        nhCauseBenefit p B1 B2) =
        ∫ x in z..T, A z * g x := by
          apply intervalIntegral.integral_congr
          intro x hx
          dsimp [A,g,nhSurvival]
          have he : Real.exp (-δ*(x-z)) *
              Real.exp (-(nhCumulative a b x-nhCumulative a b z)) =
              Real.exp (δ*z+nhCumulative a b z) *
              Real.exp (-δ*x-nhCumulative a b x) := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1
            ring
          rw [he]
          ring
      _ = A z * (∫ x in z..T, g x) := by
        simpa using (intervalIntegral.integral_const_mul (A z) g)
  have hfun : (nhDeathPV a b p δ B1 B2 T) =
      (fun z => A z * (∫ x in z..T, g x)) := by
    funext z
    exact hfact z
  rw [hfun]
  have hprod := hA.mul hI
  convert hprod using 1 <;>
    first
    | rfl
    | (funext z; dsimp; ring)
    | (rw [← hcancel]; ring)
