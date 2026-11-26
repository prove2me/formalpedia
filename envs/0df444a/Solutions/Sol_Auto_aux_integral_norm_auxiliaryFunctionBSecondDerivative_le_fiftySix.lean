-- Prove2me | solution 1 for Auto.aux_integral_norm_auxiliaryFunctionBSecondDerivative_le_fiftySix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:05:08.630461+00:00
-- url     : https://prove2.me/submissions/25bf748a-85b2-4198-a24c-3747731f14ee

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
public import Theorems.Thm_Auto_aux_auxiliaryFunctionBSecondDerivative_integrable
public import Theorems.Thm_Auto_aux_auxiliaryFunctionBSecondDerivative_eLpNorm_one_le

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution :
    (∫ ξ : ℝ, ‖auxiliaryFunctionBSecondDerivative ξ‖) ≤ 56 := by
  have h := aux_auxiliaryFunctionBSecondDerivative_eLpNorm_one_le
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm
      aux_auxiliaryFunctionBSecondDerivative_integrable] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp h
end Auto
