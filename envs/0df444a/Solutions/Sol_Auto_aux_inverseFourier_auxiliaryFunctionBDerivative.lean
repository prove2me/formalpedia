-- Prove2me | solution 1 for Auto.aux_inverseFourier_auxiliaryFunctionBDerivative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:07:37.651263+00:00
-- url     : https://prove2.me/submissions/63e6b036-0154-4091-9365-fb2ca4360f2c

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
public import Theorems.Thm_Auto_aux_auxiliaryFunctionB_integrable
public import Theorems.Thm_Auto_aux_inverseFourier_deriv
public import Theorems.Thm_Auto_aux_auxiliaryFunctionB_complex_hasDerivAt
public import Theorems.Thm_Auto_aux_deriv_auxiliaryFunctionB_complex
public import Theorems.Thm_Auto_aux_deriv_auxiliaryFunctionB_complex_integrable

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (x : ℝ) :
    FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionBDerivative ξ : ℂ)) x =
      (-(2 * Real.pi * Complex.I * x)) *
        FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x := by
  have hderiv : deriv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) =
      fun ξ : ℝ => (auxiliaryFunctionBDerivative ξ : ℂ) := by
    funext ξ
    exact aux_deriv_auxiliaryFunctionB_complex ξ
  rw [← hderiv]
  exact aux_inverseFourier_deriv (f := fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ))
    aux_auxiliaryFunctionB_integrable.ofReal
    (fun ξ => (aux_auxiliaryFunctionB_complex_hasDerivAt ξ).differentiableAt)
    aux_deriv_auxiliaryFunctionB_complex_integrable x
end Auto
