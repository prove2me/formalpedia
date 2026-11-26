-- Prove2me | solution 1 for Auto.aux_inverseFourier_deriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:50:34.229851+00:00
-- url     : https://prove2.me/submissions/e864bc24-5800-40bd-8ff7-f93e5a78f674

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

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution {f : ℝ → ℂ}
    (hf : Integrable f) (h'f : Differentiable ℝ f) (hf' : Integrable (deriv f)) (x : ℝ) :
    FourierTransformInv.fourierInv (deriv f) x =
      (-(2 * Real.pi * Complex.I * x)) * FourierTransformInv.fourierInv f x := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_deriv hf h'f hf']
  simp only [smul_eq_mul, neg_mul]
  rw [← Real.fourierInv_eq_fourier_neg]
  push_cast
  ring
end Auto
