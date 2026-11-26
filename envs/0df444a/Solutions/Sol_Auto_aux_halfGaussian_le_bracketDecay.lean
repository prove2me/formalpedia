-- Prove2me | solution 1 for Auto.aux_halfGaussian_le_bracketDecay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:56:50.269797+00:00
-- url     : https://prove2.me/submissions/9f9639de-1360-4a36-9f53-68eff94dada2

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
public import Theorems.Thm_Auto_aux_abs_pow_mul_exp_neg_half_le

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (x : ℝ) (n : ℕ) :
    Real.exp (-(Real.pi / 2) * x ^ 2) ≤
      (4 * ((n + 1 : ℕ) : ℝ)) ^ ((n : ℝ) / 2) * bracketBump x ^ n := by
  have hden : 0 < (1 + |x|) ^ n := pow_pos (by positivity) _
  have htwo : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    calc
      (4 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 4 := (Real.sqrt_eq_rpow 4).symm
      _ = 2 := by norm_num
  have htwoPowEq : (2 : ℝ) ^ n = (4 : ℝ) ^ ((n : ℝ) / 2) := by
    calc
      (2 : ℝ) ^ n = (2 : ℝ) ^ (n : ℝ) := (Real.rpow_natCast 2 n).symm
      _ = ((4 : ℝ) ^ (1 / 2 : ℝ)) ^ (n : ℝ) := by rw [htwo]
      _ = (4 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ)) :=
        (Real.rpow_mul (by norm_num) (1 / 2 : ℝ) (n : ℝ)).symm
      _ = (4 : ℝ) ^ ((n : ℝ) / 2) := by congr 1; ring
  have htwopow : (2 : ℝ) ^ n ≤
      (4 * ((n + 1 : ℕ) : ℝ)) ^ ((n : ℝ) / 2) := by
    have hbase : (4 : ℝ) ≤ 4 * ((n + 1 : ℕ) : ℝ) := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      push_cast
      nlinarith
    calc
      (2 : ℝ) ^ n = (4 : ℝ) ^ ((n : ℝ) / 2) := htwoPowEq
      _ ≤ (4 * ((n + 1 : ℕ) : ℝ)) ^ ((n : ℝ) / 2) :=
        Real.rpow_le_rpow (by norm_num) hbase (by positivity)
  have hcore : Real.exp (-(Real.pi / 2) * x ^ 2) * (1 + |x|) ^ n ≤
      (4 * ((n + 1 : ℕ) : ℝ)) ^ ((n : ℝ) / 2) := by
    by_cases hx : |x| ≤ 1
    · have hexp : Real.exp (-(Real.pi / 2) * x ^ 2) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, sq_nonneg x])
      have hbase : 1 + |x| ≤ 2 := by linarith
      have hpow : (1 + |x|) ^ n ≤ (2 : ℝ) ^ n := by gcongr
      calc
        Real.exp (-(Real.pi / 2) * x ^ 2) * (1 + |x|) ^ n ≤
            1 * (1 + |x|) ^ n :=
          mul_le_mul_of_nonneg_right hexp (pow_nonneg (by positivity) _)
        _ = (1 + |x|) ^ n := by ring
        _ ≤ (2 : ℝ) ^ n := hpow
        _ ≤ (4 * ((n + 1 : ℕ) : ℝ)) ^ ((n : ℝ) / 2) := htwopow
    · have hxone : 1 ≤ |x| := le_of_not_ge hx
      have hbase : 1 + |x| ≤ 2 * |x| := by linarith
      have hpow : (1 + |x|) ^ n ≤ (2 * |x|) ^ n := by gcongr
      have habs := aux_abs_pow_mul_exp_neg_half_le n x
      have hExpPi : Real.exp (-1) ≤ Real.pi := by
        exact (Real.exp_le_one_iff.mpr (by norm_num)).trans (by nlinarith [Real.pi_gt_three])
      have hmul : ((n + 1 : ℕ) : ℝ) * Real.exp (-1) ≤ ((n + 1 : ℕ) : ℝ) * Real.pi :=
        mul_le_mul_of_nonneg_left hExpPi (by positivity)
      have hsmallbase : ((n + 1 : ℕ) : ℝ) * Real.exp (-1) / Real.pi ≤ ((n + 1 : ℕ) : ℝ) := by
        calc
          ((n + 1 : ℕ) : ℝ) * Real.exp (-1) / Real.pi ≤
              (((n + 1 : ℕ) : ℝ) * Real.pi) / Real.pi :=
            div_le_div_of_nonneg_right hmul Real.pi_pos.le
          _ = ((n + 1 : ℕ) : ℝ) := by field_simp
      have hB :
          (((n + 1 : ℕ) : ℝ) * Real.exp (-1) / Real.pi) ^ ((n : ℝ) / 2) ≤
            ((n + 1 : ℕ) : ℝ) ^ ((n : ℝ) / 2) :=
        Real.rpow_le_rpow (by positivity) hsmallbase (by positivity)
      have hfinal : (2 : ℝ) ^ n *
            (((n + 1 : ℕ) : ℝ) * Real.exp (-1) / Real.pi) ^ ((n : ℝ) / 2) ≤
            (4 * ((n + 1 : ℕ) : ℝ)) ^ ((n : ℝ) / 2) := by
        calc
          (2 : ℝ) ^ n *
              (((n + 1 : ℕ) : ℝ) * Real.exp (-1) / Real.pi) ^ ((n : ℝ) / 2) ≤
              (2 : ℝ) ^ n * ((n + 1 : ℕ) : ℝ) ^ ((n : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left hB (pow_nonneg (by positivity) _)
          _ = (4 : ℝ) ^ ((n : ℝ) / 2) * ((n + 1 : ℕ) : ℝ) ^ ((n : ℝ) / 2) := by
            rw [htwoPowEq]
          _ = (4 * ((n + 1 : ℕ) : ℝ)) ^ ((n : ℝ) / 2) :=
            (Real.mul_rpow (by norm_num) (by positivity)).symm
      calc
        Real.exp (-(Real.pi / 2) * x ^ 2) * (1 + |x|) ^ n ≤
            Real.exp (-(Real.pi / 2) * x ^ 2) * (2 * |x|) ^ n :=
          mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
        _ = (2 : ℝ) ^ n * (|x| ^ n * Real.exp (-(Real.pi / 2) * x ^ 2)) := by
          rw [mul_pow]
          ring
        _ ≤ (2 : ℝ) ^ n *
            (((n + 1 : ℕ) : ℝ) * Real.exp (-1) / Real.pi) ^ ((n : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left habs (pow_nonneg (by positivity) _)
        _ ≤ (4 * ((n + 1 : ℕ) : ℝ)) ^ ((n : ℝ) / 2) := hfinal
  have h : Real.exp (-(Real.pi / 2) * x ^ 2) ≤
      (4 * ((n + 1 : ℕ) : ℝ)) ^ ((n : ℝ) / 2) / (1 + |x|) ^ n := by
    calc
      Real.exp (-(Real.pi / 2) * x ^ 2) =
          (Real.exp (-(Real.pi / 2) * x ^ 2) * (1 + |x|) ^ n) / (1 + |x|) ^ n := by
        field_simp [ne_of_gt hden]
      _ ≤ (4 * ((n + 1 : ℕ) : ℝ)) ^ ((n : ℝ) / 2) / (1 + |x|) ^ n :=
        div_le_div_of_nonneg_right hcore hden.le
  simpa only [bracketBump, inv_pow, div_eq_mul_inv] using h
end Auto
