-- Prove2me | solution 1 for Auto.aux_exp_three_half_pi_sq_le_nine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:58:52.15118+00:00
-- url     : https://prove2.me/submissions/a2cefe58-2f88-4daa-a603-00e8303e9c5b

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
theorem _root_.solution {x : ℝ} (hx : |x| ≤ 1 / 2) :
    Real.exp (3 * (Real.pi * x ^ 2) / 2) ≤ 9 := by
  have hx2 : x ^ 2 ≤ 1 / 4 := by
    have h : |x| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg x) (by norm_num)).2 hx
    rw [sq_abs] at h
    norm_num at h ⊢
    exact h
  have hu : Real.pi * x ^ 2 ≤ 1 := by
    calc
      Real.pi * x ^ 2 ≤ 4 * x ^ 2 :=
        mul_le_mul_of_nonneg_right Real.pi_le_four (sq_nonneg x)
      _ ≤ 4 * (1 / 4) := mul_le_mul_of_nonneg_left hx2 (by norm_num)
      _ = 1 := by norm_num
  calc
    Real.exp (3 * (Real.pi * x ^ 2) / 2) ≤ Real.exp 2 :=
      Real.exp_le_exp.mpr (by nlinarith)
    _ = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      congr 1; norm_num
    _ ≤ 3 * 3 := mul_le_mul (le_of_lt Real.exp_one_lt_three)
      (le_of_lt Real.exp_one_lt_three) (Real.exp_pos _).le (by norm_num)
    _ = 9 := by norm_num
end Auto
