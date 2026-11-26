-- Prove2me | solution 1 for Auto.aux_auxiliaryFunctionBSecondDerivative_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:02:57.0928+00:00
-- url     : https://prove2.me/submissions/05baee1b-96e3-44fe-983f-f62d140e3efe

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
public import Theorems.Thm_Auto_aux_auxiliaryFunctionBSecondDerivative_norm_le_sharp
public import Theorems.Thm_Auto_aux_BSecondSharpMajorant_integrable
public import Theorems.Thm_Auto_aux_auxiliaryFunctionBSecondDerivative_measurable

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution :
    Integrable auxiliaryFunctionBSecondDerivative := by
  exact aux_BSecondSharpMajorant_integrable.mono'
    aux_auxiliaryFunctionBSecondDerivative_measurable.aestronglyMeasurable
    (ae_of_all _ aux_auxiliaryFunctionBSecondDerivative_norm_le_sharp)
end Auto
