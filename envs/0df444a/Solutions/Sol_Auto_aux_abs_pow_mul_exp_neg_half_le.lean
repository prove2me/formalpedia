-- Prove2me | solution 1 for Auto.aux_abs_pow_mul_exp_neg_half_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:54:47.930055+00:00
-- url     : https://prove2.me/submissions/75dc2d54-88e2-4007-a676-dfa065f5b06a

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
public import Theorems.Thm_Auto_aux_pow_mul_exp_neg_le

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (d : ℕ) (x : ℝ) :
    |x| ^ d * Real.exp (-(Real.pi / 2) * x ^ 2) ≤
      Real.rpow (((d + 1 : ℕ) : ℝ) * Real.exp (-1) / Real.pi) ((d : ℝ) / 2) := by
  let B : ℝ := ((d + 1 : ℕ) : ℝ) * Real.exp (-1) / Real.pi
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hsquared : (|x| ^ d * Real.exp (-(Real.pi / 2) * x ^ 2)) ^ 2 ≤
      ((d : ℝ) * Real.exp (-1) / Real.pi) ^ d := by
    have h := aux_pow_mul_exp_neg_le d (Real.pi * x ^ 2) (by positivity)
    have h' : (Real.pi * x ^ 2) ^ d * Real.exp (-Real.pi * x ^ 2) ≤
        ((d : ℝ) * Real.exp (-1)) ^ d := by
      simpa using h
    calc
      (|x| ^ d * Real.exp (-(Real.pi / 2) * x ^ 2)) ^ 2 =
          (1 / Real.pi) ^ d * ((Real.pi * x ^ 2) ^ d * Real.exp (-Real.pi * x ^ 2)) := by
        rw [mul_pow, ← Real.exp_nat_mul, ← pow_mul]
        rw [show (d : ℕ) * 2 = 2 * d by omega, pow_mul, sq_abs]
        rw [mul_pow, div_pow]
        field_simp [Real.pi_ne_zero]
        ring_nf
      _ ≤ (1 / Real.pi) ^ d * ((d : ℝ) * Real.exp (-1)) ^ d :=
        mul_le_mul_of_nonneg_left h' (by positivity)
      _ = ((d : ℝ) * Real.exp (-1) / Real.pi) ^ d := by
        rw [div_pow]
        ring
  have hbase : (d : ℝ) * Real.exp (-1) / Real.pi ≤ B := by
    dsimp [B]
    have hd : (d : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ d
    gcongr
  have hBsquared : (|x| ^ d * Real.exp (-(Real.pi / 2) * x ^ 2)) ^ 2 ≤ B ^ d :=
    hsquared.trans (by gcongr)
  have hrpow_sq : (Real.rpow B ((d : ℝ) / 2)) ^ 2 = B ^ d := by
    calc
      (Real.rpow B ((d : ℝ) / 2)) ^ 2 =
          Real.rpow B ((d : ℝ) / 2) * Real.rpow B ((d : ℝ) / 2) := by ring
      _ = Real.rpow B ((d : ℝ) / 2 + (d : ℝ) / 2) :=
        (Real.rpow_add hB _ _).symm
      _ = Real.rpow B (d : ℝ) := by congr 1; ring
      _ = B ^ d := Real.rpow_natCast B d
  have habs : |(|x| ^ d * Real.exp (-(Real.pi / 2) * x ^ 2))| ≤
      |Real.rpow B ((d : ℝ) / 2)| := by
    apply (sq_le_sq).mp
    rw [hrpow_sq]
    exact hBsquared
  have hRpos : 0 < Real.rpow B ((d : ℝ) / 2) := Real.rpow_pos_of_pos hB _
  change |x| ^ d * Real.exp (-(Real.pi / 2) * x ^ 2) ≤ Real.rpow B ((d : ℝ) / 2)
  calc
    |x| ^ d * Real.exp (-(Real.pi / 2) * x ^ 2) =
        |(|x| ^ d * Real.exp (-(Real.pi / 2) * x ^ 2))| :=
      (abs_of_nonneg (by positivity)).symm
    _ ≤ |Real.rpow B ((d : ℝ) / 2)| := habs
    _ = Real.rpow B ((d : ℝ) / 2) := abs_of_pos hRpos
end Auto
