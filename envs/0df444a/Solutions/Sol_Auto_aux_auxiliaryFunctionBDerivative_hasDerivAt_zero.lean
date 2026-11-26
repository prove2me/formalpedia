-- Prove2me | solution 1 for Auto.aux_auxiliaryFunctionBDerivative_hasDerivAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:04:13.125221+00:00
-- url     : https://prove2.me/submissions/72052c3b-4b47-4b5a-9431-a28d1a01b697

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
public import Theorems.Thm_Auto_aux_auxiliaryFunctionBDerivative_continuous
public import Theorems.Thm_Auto_aux_auxiliaryFunctionBDerivative_hasDerivAt_of_ne_zero
public import Theorems.Thm_Auto_aux_auxiliaryFunctionBTrueSecondDerivative_continuousAt_zero

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution :
    HasDerivAt auxiliaryFunctionBDerivative (-Real.pi) 0 := by
  have h := hasDerivAt_of_hasDerivAt_of_ne
    (f := auxiliaryFunctionBDerivative)
    (g := fun x : ℝ =>
      if x = 0 then -Real.pi else auxiliaryFunctionBSecondDerivative x)
    (x := 0)
    (fun y hy => by
      simpa [hy] using aux_auxiliaryFunctionBDerivative_hasDerivAt_of_ne_zero hy)
    aux_auxiliaryFunctionBDerivative_continuous.continuousAt
    aux_auxiliaryFunctionBTrueSecondDerivative_continuousAt_zero
  simpa using h
end Auto
