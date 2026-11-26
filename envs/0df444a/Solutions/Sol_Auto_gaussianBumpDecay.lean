-- Prove2me | solution 1 for Auto.gaussianBumpDecay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:08:14.680864+00:00
-- url     : https://prove2.me/submissions/a129692e-bdcb-4513-b6b0-5e9940167a20

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
public import Theorems.Thm_Auto_aux_halfGaussian_le_bracketDecay
public import Theorems.Thm_Auto_aux_gaussian_iteratedDeriv_half_decay

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (x : ℝ) (m N : ℕ) :
    |iteratedDeriv m gaussian x| ≤ C_gaussianBumpDecay m N * bracketBump x ^ N := by
  let A : ℝ := Real.rpow (38 * ((m + 1 : ℕ) : ℝ)) ((m : ℝ) / 2)
  let B : ℝ := Real.rpow (4 * ((N + 1 : ℕ) : ℝ)) ((N : ℝ) / 2)
  have hderiv : |iteratedDeriv m gaussian x| ≤
      A * Real.exp (-(Real.pi / 2) * x ^ 2) := by
    simpa only [A, Real.rpow_eq_pow] using aux_gaussian_iteratedDeriv_half_decay m x
  have hdecay : Real.exp (-(Real.pi / 2) * x ^ 2) ≤ B * bracketBump x ^ N := by
    simpa only [B, Real.rpow_eq_pow] using aux_halfGaussian_le_bracketDecay x N
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  calc
    |iteratedDeriv m gaussian x| ≤
        A * Real.exp (-(Real.pi / 2) * x ^ 2) := hderiv
    _ ≤ A * (B * bracketBump x ^ N) :=
      mul_le_mul_of_nonneg_left hdecay hA
    _ = C_gaussianBumpDecay m N * bracketBump x ^ N := by
      dsimp [A, B, C_gaussianBumpDecay]
      ring
end Auto
