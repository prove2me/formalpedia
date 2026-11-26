-- Prove2me | solution 1 for Auto.aux_exp_three_half_pi_sq_le_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:58:56.050996+00:00
-- url     : https://prove2.me/submissions/e6f08625-3435-41ac-8f43-e2efb6528d43

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
    Real.exp (3 * (Real.pi * x ^ 2) / 2) ≤ 4 := by
  have hx2 : x ^ 2 ≤ 1 / 4 := by
    have h : |x| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg x) (by norm_num)).2 hx
    rw [sq_abs] at h
    norm_num at h ⊢
    exact h
  have hu0 : 0 ≤ 3 * (Real.pi * x ^ 2) / 2 := by positivity
  have hu : 3 * (Real.pi * x ^ 2) / 2 ≤ 6 / 5 := by
    have hpi : Real.pi ≤ 63 / 20 := by nlinarith [Real.pi_lt_d2]
    nlinarith [mul_le_mul_of_nonneg_left hx2 Real.pi_pos.le,
      mul_le_mul_of_nonneg_right hpi (sq_nonneg x)]
  calc
    Real.exp (3 * (Real.pi * x ^ 2) / 2) ≤
        (2 + 3 * (Real.pi * x ^ 2) / 2) / (2 - 3 * (Real.pi * x ^ 2) / 2) :=
      Real.exp_le_two_add_div_two_sub hu0 (by linarith)
    _ ≤ 4 := by
      apply (div_le_iff₀ (by linarith : 0 < 2 - 3 * (Real.pi * x ^ 2) / 2)).2
      nlinarith
end Auto
