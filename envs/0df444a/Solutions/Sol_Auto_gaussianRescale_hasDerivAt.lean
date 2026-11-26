-- Prove2me | solution 1 for Auto.gaussianRescale_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:54:59.115926+00:00
-- url     : https://prove2.me/submissions/7d2f9223-2ccb-41c1-a251-bf7fcae4f67d

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
public import Theorems.Thm_Auto_aux_gaussian_hasDerivAt

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (t x : ℝ) :
    HasDerivAt (gaussianRescale t)
      (t⁻¹ * (-2 * Real.pi * (t⁻¹ * x) * gaussian (t⁻¹ * x)) * t⁻¹) x := by
  have hlinear : HasDerivAt (fun y : ℝ => t⁻¹ * y) t⁻¹ x := hasDerivAt_const_mul t⁻¹
  have hcomposed := (aux_gaussian_hasDerivAt (t⁻¹ * x)).comp x hlinear
  have hscaled := hcomposed.const_mul t⁻¹
  change HasDerivAt (fun y : ℝ => t⁻¹ * gaussian (t⁻¹ * y))
    (t⁻¹ * (-2 * Real.pi * (t⁻¹ * x) * gaussian (t⁻¹ * x)) * t⁻¹) x
  convert hscaled using 1 <;> first | rfl | ring
end Auto
