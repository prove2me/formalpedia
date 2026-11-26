-- Prove2me | solution 1 for Auto.gaussianRescale_deriv_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:09:07.952156+00:00
-- url     : https://prove2.me/submissions/a9796f6d-ace6-436e-809d-6f67cf7da3fd

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
public import Theorems.Thm_Auto_gaussianRescale_hasDerivAt
public import Theorems.Thm_Auto_aux_gaussian_deriv_le_C_gaussianBumpDecay_one_two

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution {t x : ℝ} (ht : 0 < t) :
    |deriv (gaussianRescale t) x| ≤
      t⁻¹ * C_gaussianBumpDecay 1 2 * scaledBracketBump 2 t x := by
  rw [(gaussianRescale_hasDerivAt t x).deriv]
  have htin : 0 ≤ t⁻¹ := inv_nonneg.mpr ht.le
  have hbase := aux_gaussian_deriv_le_C_gaussianBumpDecay_one_two (t⁻¹ * x)
  calc
    |t⁻¹ * (-2 * Real.pi * (t⁻¹ * x) * gaussian (t⁻¹ * x)) * t⁻¹| =
        t⁻¹ * |-2 * Real.pi * (t⁻¹ * x) * gaussian (t⁻¹ * x)| * t⁻¹ := by
      rw [abs_mul, abs_mul, abs_of_nonneg htin]
    _ ≤ t⁻¹ * (C_gaussianBumpDecay 1 2 * bracketBump (t⁻¹ * x) ^ 2) * t⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbase htin) htin
    _ = t⁻¹ * C_gaussianBumpDecay 1 2 * scaledBracketBump 2 t x := by
      unfold scaledBracketBump
      simp only [bracketBump]
      ring
end Auto
