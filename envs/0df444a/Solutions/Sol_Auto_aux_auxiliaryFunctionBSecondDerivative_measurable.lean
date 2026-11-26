-- Prove2me | solution 1 for Auto.aux_auxiliaryFunctionBSecondDerivative_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:49:50.088403+00:00
-- url     : https://prove2.me/submissions/7e8cc69d-0ffc-4bd6-808d-45032336f7f7

module
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Definitions.Def_LeanNct_Auto_Preliminaries_Notation
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
public import Definitions.Def_LeanNct_Auto_Preliminaries_Gaussians
public import Theorems.Thm_Auto_gaussian_continuous
public import Theorems.Thm_Auto_continuous_sqrtOneMinusGaussian

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution :
    Measurable auxiliaryFunctionBSecondDerivative := by
  unfold auxiliaryFunctionBSecondDerivative
  apply Measurable.ite
    (by simpa only [Set.ofPred_eq_eq_singleton] using (measurableSet_singleton (0 : ℝ)))
  · exact measurable_const
  · have hg : Measurable gaussian := gaussian_continuous.measurable
    have hf : Measurable sqrtOneMinusGaussian :=
      continuous_sqrtOneMinusGaussian.measurable
    have hpoly : Measurable (fun x : ℝ =>
        4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) := by
      exact (measurable_const.mul (measurable_id'.pow_const 2)).sub measurable_const
    have htermone : Measurable (fun x : ℝ =>
        ((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
          (2 * sqrtOneMinusGaussian x)) :=
      (hpoly.mul hg).div (measurable_const.mul hf)
    have hlinear : Measurable (fun x : ℝ => -2 * Real.pi * x * gaussian x) :=
      (measurable_const.mul measurable_id').mul hg
    have htermtwo : Measurable (fun x : ℝ =>
        (-2 * Real.pi * x * gaussian x) ^ 2 /
          (4 * sqrtOneMinusGaussian x ^ 3)) :=
      (hlinear.pow_const 2).div (measurable_const.mul (hf.pow_const 3))
    have habel : Measurable (fun x : ℝ =>
        Real.pi * Real.exp (-|Real.sqrt Real.pi * x|)) :=
      measurable_const.mul ((measurable_const.mul measurable_id').abs.neg.exp)
    exact (htermone.add htermtwo).sub habel
end Auto
