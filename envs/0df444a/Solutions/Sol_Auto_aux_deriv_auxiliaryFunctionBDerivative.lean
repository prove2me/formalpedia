-- Prove2me | solution 1 for Auto.aux_deriv_auxiliaryFunctionBDerivative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:11:50.573233+00:00
-- url     : https://prove2.me/submissions/827ecdaa-8754-411e-85de-b168ca95b3ce

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
public import Theorems.Thm_Auto_aux_auxiliaryFunctionBDerivative_hasDerivAt_of_ne_zero
public import Theorems.Thm_Auto_aux_auxiliaryFunctionBDerivative_hasDerivAt_zero

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (x : ℝ) :
    deriv auxiliaryFunctionBDerivative x =
      if x = 0 then -Real.pi else auxiliaryFunctionBSecondDerivative x := by
  by_cases hx : x = 0
  · subst x
    simpa using aux_auxiliaryFunctionBDerivative_hasDerivAt_zero.deriv
  · simpa [hx] using (aux_auxiliaryFunctionBDerivative_hasDerivAt_of_ne_zero hx).deriv
end Auto
