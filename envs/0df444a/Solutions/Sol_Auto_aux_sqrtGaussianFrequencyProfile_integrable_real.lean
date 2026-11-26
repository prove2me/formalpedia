-- Prove2me | solution 1 for Auto.aux_sqrtGaussianFrequencyProfile_integrable_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:46:05.753708+00:00
-- url     : https://prove2.me/submissions/aab750a2-af83-421f-93d4-516e857df5f3

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
public import Theorems.Thm_Auto_aux_gaussian_integrable
public import Theorems.Thm_Auto_continuous_sqrtOneMinusGaussian
public import Theorems.Thm_Auto_aux_one_sub_sqrtOneMinusGaussian_nonneg
public import Theorems.Thm_Auto_aux_one_sub_sqrtOneMinusGaussian_le_gaussian

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution :
    Integrable (fun ξ : ℝ => 1 - sqrtOneMinusGaussian ξ) := by
  refine aux_gaussian_integrable.mono_nonneg
    (continuous_const.sub continuous_sqrtOneMinusGaussian).aestronglyMeasurable
    (ae_of_all _ aux_one_sub_sqrtOneMinusGaussian_nonneg)
    (ae_of_all _ aux_one_sub_sqrtOneMinusGaussian_le_gaussian)
end Auto
