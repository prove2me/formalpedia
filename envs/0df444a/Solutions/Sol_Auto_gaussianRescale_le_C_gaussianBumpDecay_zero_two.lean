-- Prove2me | solution 1 for Auto.gaussianRescale_le_C_gaussianBumpDecay_zero_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:08:35.528726+00:00
-- url     : https://prove2.me/submissions/e9c2518d-785e-4e26-9a84-eb2aea13c9ec

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
public import Theorems.Thm_Auto_aux_gaussian_le_four_bracket_sq

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution {t x : ℝ} (ht : 0 < t) :
    |gaussianRescale t x| ≤
      C_gaussianBumpDecay 0 2 * scaledBracketBump 2 t x := by
  rw [gaussianRescale,
    abs_of_nonneg (mul_nonneg (inv_nonneg.mpr ht.le) (aux_gaussian_pos _).le)]
  change t⁻¹ * gaussian (t⁻¹ * x) ≤
    C_gaussianBumpDecay 0 2 * (t⁻¹ * bracketBump (t⁻¹ * x) ^ 2)
  have hC : (4 : ℝ) ≤ C_gaussianBumpDecay 0 2 := by
    norm_num [C_gaussianBumpDecay, Real.rpow_one]
  calc
    t⁻¹ * gaussian (t⁻¹ * x) ≤ t⁻¹ * (4 * bracketBump (t⁻¹ * x) ^ 2) :=
      mul_le_mul_of_nonneg_left (aux_gaussian_le_four_bracket_sq (t⁻¹ * x))
        (inv_nonneg.mpr ht.le)
    _ ≤ t⁻¹ * (C_gaussianBumpDecay 0 2 * bracketBump (t⁻¹ * x) ^ 2) := by
      gcongr
    _ = C_gaussianBumpDecay 0 2 * (t⁻¹ * bracketBump (t⁻¹ * x) ^ 2) := by ring
end Auto
