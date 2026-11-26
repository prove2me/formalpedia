-- Prove2me | solution 1 for Auto.aux_auxiliaryFunctionB_eq_fourierPoisson
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:10:24.611119+00:00
-- url     : https://prove2.me/submissions/d1743eda-5a32-4e07-9b0e-38b987205f2c

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
public import Theorems.Thm_Auto_poissonKernel_fourier

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (ξ : ℝ) :
    auxiliaryFunctionB ξ = 1 - sqrtOneMinusGaussian ξ -
      (FourierTransform.fourier (fun x : ℝ => (poissonKernel x : ℂ))
        (Real.sqrt Real.pi * ξ)).re := by
  rw [poissonKernel_fourier]
  change 1 - sqrtOneMinusGaussian ξ - Real.exp (-|Real.sqrt Real.pi * ξ|) =
    1 - sqrtOneMinusGaussian ξ -
      (Complex.exp ((- |Real.sqrt Real.pi * ξ| : ℝ) : ℂ)).re
  rw [Complex.exp_ofReal_re]
end Auto
