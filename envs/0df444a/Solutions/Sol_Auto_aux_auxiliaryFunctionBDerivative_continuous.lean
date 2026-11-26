-- Prove2me | solution 1 for Auto.aux_auxiliaryFunctionBDerivative_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:01:18.494204+00:00
-- url     : https://prove2.me/submissions/c380c8d2-1d2b-4cf7-81fb-69ba3dcfd3c2

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
public import Theorems.Thm_Auto_aux_auxiliaryFunctionBDerivative_continuousAt_of_ne_zero
public import Theorems.Thm_Auto_aux_auxiliaryFunctionBDerivative_tendsto_zero

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution : Continuous auxiliaryFunctionBDerivative := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  by_cases hx : x = 0
  · subst x
    rw [continuousAt_iff_punctured_nhds]
    simpa [auxiliaryFunctionBDerivative] using aux_auxiliaryFunctionBDerivative_tendsto_zero
  · exact aux_auxiliaryFunctionBDerivative_continuousAt_of_ne_zero hx
end Auto
