-- Prove2me | solution 1 for Auto.aux_auxiliaryFunctionBDerivative_gaussianTerm_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:57:48.112835+00:00
-- url     : https://prove2.me/submissions/64a745e5-1054-4170-b825-133597c6c838

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
public import Theorems.Thm_Auto_aux_gaussian_pos
public import Theorems.Thm_Auto_aux_sqrtOneMinusGaussian_pos
public import Theorems.Thm_Auto_aux_sqrtOneMinusGaussian_lower

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution {x : ℝ} (hx : x ≠ 0) :
    |(-2 * Real.pi * x * gaussian x) / (2 * sqrtOneMinusGaussian x)| ≤
      Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2) := by
  have hroot : 0 < sqrtOneMinusGaussian x := aux_sqrtOneMinusGaussian_pos hx
  have hden : 0 < 2 * sqrtOneMinusGaussian x := by positivity
  have hhalf_sq : Real.exp (-(Real.pi / 2) * x ^ 2) ^ 2 = gaussian x := by
    change Real.exp (-(Real.pi / 2) * x ^ 2) ^ 2 =
      Real.exp (-Real.pi * x ^ 2)
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [abs_div, abs_mul, abs_mul, abs_mul, abs_neg,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg Real.pi_pos.le,
    abs_of_nonneg (aux_gaussian_pos x).le,
    abs_of_nonneg (by positivity : 0 ≤ 2 * sqrtOneMinusGaussian x)]
  apply (div_le_iff₀ hden).2
  have hmul := mul_le_mul_of_nonneg_left (aux_sqrtOneMinusGaussian_lower x)
    (show 0 ≤ 2 * Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2) by positivity)
  have hsqrtpi : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
    Real.sq_sqrt (le_of_lt Real.pi_pos)
  calc
    2 * Real.pi * |x| * gaussian x =
        (2 * Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2)) *
          (Real.sqrt Real.pi * |x| * Real.exp (-(Real.pi / 2) * x ^ 2)) := by
      rw [← hhalf_sq]
      calc
        2 * Real.pi * |x| * Real.exp (-(Real.pi / 2) * x ^ 2) ^ 2 =
            2 * (Real.sqrt Real.pi) ^ 2 * |x| *
              Real.exp (-(Real.pi / 2) * x ^ 2) ^ 2 := by rw [hsqrtpi]
        _ = (2 * Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2)) *
              (Real.sqrt Real.pi * |x| * Real.exp (-(Real.pi / 2) * x ^ 2)) := by ring
    _ ≤ (2 * Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2)) *
          sqrtOneMinusGaussian x := hmul
    _ = (Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2)) *
          (2 * sqrtOneMinusGaussian x) := by ring
end Auto
