-- Prove2me | solution 1 for Auto.aux_BDerivative_gaussianTerm_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:02:26.369329+00:00
-- url     : https://prove2.me/submissions/160916a8-263e-4bd6-85f6-8637500b9bb7

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
public import Theorems.Thm_Auto_aux_sqrtOneMinusGaussian_pos
public import Theorems.Thm_Auto_aux_gaussian_deriv_hasDerivAt
public import Theorems.Thm_Auto_aux_sqrtOneMinusGaussian_hasDerivAt

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ =>
      (-2 * Real.pi * y * gaussian y) / (2 * sqrtOneMinusGaussian y))
      (((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
          (2 * sqrtOneMinusGaussian x) +
        (-2 * Real.pi * x * gaussian x) ^ 2 /
          (4 * sqrtOneMinusGaussian x ^ 3)) x := by
  have hroot : sqrtOneMinusGaussian x ≠ 0 :=
    (aux_sqrtOneMinusGaussian_pos hx).ne'
  have hu := aux_gaussian_deriv_hasDerivAt x
  have hf := aux_sqrtOneMinusGaussian_hasDerivAt hx
  have hden : 2 * sqrtOneMinusGaussian x ≠ 0 :=
    mul_ne_zero two_ne_zero hroot
  have hraw := hu.div (hf.const_mul 2) hden
  have hfun : (fun y : ℝ =>
      (-2 * Real.pi * y * gaussian y) / (2 * sqrtOneMinusGaussian y)) =ᶠ[𝓝 x]
      ((fun y : ℝ => -2 * Real.pi * y * gaussian y) /
        (fun y : ℝ => 2 * sqrtOneMinusGaussian y)) := by
    filter_upwards [] with y
    rfl
  have hraw' := hraw.congr_of_eventuallyEq hfun
  have hcoef :
      (((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) *
          (2 * sqrtOneMinusGaussian x) -
        (-2 * Real.pi * x * gaussian x) *
          (2 * ((2 * Real.pi * x * gaussian x) /
            (2 * sqrtOneMinusGaussian x)))) /
          (2 * sqrtOneMinusGaussian x) ^ 2 =
        ((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
            (2 * sqrtOneMinusGaussian x) +
          (-2 * Real.pi * x * gaussian x) ^ 2 /
            (4 * sqrtOneMinusGaussian x ^ 3) := by
    field_simp [hroot]
    ring
  rw [hcoef] at hraw'
  exact hraw'
end Auto
