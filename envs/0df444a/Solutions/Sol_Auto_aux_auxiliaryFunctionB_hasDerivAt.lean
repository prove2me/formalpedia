-- Prove2me | solution 1 for Auto.aux_auxiliaryFunctionB_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:03:01.605411+00:00
-- url     : https://prove2.me/submissions/1c68ee67-f527-48a0-9e38-9d7321082130

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
public import Theorems.Thm_Auto_aux_auxiliaryFunctionB_continuous
public import Theorems.Thm_Auto_aux_auxiliaryFunctionB_hasDerivAt_of_ne_zero
public import Theorems.Thm_Auto_aux_auxiliaryFunctionBDerivative_continuous

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (x : ℝ) :
    HasDerivAt auxiliaryFunctionB (auxiliaryFunctionBDerivative x) x := by
  by_cases hx : x = 0
  · subst x
    exact hasDerivAt_of_hasDerivAt_of_ne
      (fun y hy => aux_auxiliaryFunctionB_hasDerivAt_of_ne_zero hy)
      aux_auxiliaryFunctionB_continuous.continuousAt
      aux_auxiliaryFunctionBDerivative_continuous.continuousAt
  · exact aux_auxiliaryFunctionB_hasDerivAt_of_ne_zero hx
end Auto
