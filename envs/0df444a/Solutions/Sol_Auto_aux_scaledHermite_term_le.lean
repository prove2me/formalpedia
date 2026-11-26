-- Prove2me | solution 1 for Auto.aux_scaledHermite_term_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:54:12.545874+00:00
-- url     : https://prove2.me/submissions/d937c536-8aa5-42e9-bca9-7918297a1d8e

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
theorem _root_.solution (m j d : Nat) (hm : m = 2 * j + d) :
    (Real.sqrt (2 * Real.pi)) ^ m * ((2 : Real) ^ (j + d) * (m : Real) ^ j) *
        (Real.sqrt (2 * Real.pi)) ^ d *
        (((d + 1 : Nat) : Real) * Real.exp (-1) / Real.pi) ^ ((d : Real) / 2) ≤
      (19 * ((m + 1 : Nat) : Real)) ^ ((m : Real) / 2) := by
  subst m
  have hsd :
      (Real.sqrt (2 * Real.pi)) ^ (2 * j + d) * (Real.sqrt (2 * Real.pi)) ^ d =
        (2 * Real.pi) ^ (j + d) := by
    have hsquare : (Real.sqrt (2 * Real.pi)) ^ 2 = 2 * Real.pi :=
      Real.sq_sqrt (by positivity)
    have hleft : (Real.sqrt (2 * Real.pi)) ^ (2 * j) =
        ((Real.sqrt (2 * Real.pi)) ^ 2) ^ j := by rw [pow_mul]
    have hright : (Real.sqrt (2 * Real.pi)) ^ d * (Real.sqrt (2 * Real.pi)) ^ d =
        ((Real.sqrt (2 * Real.pi)) ^ 2) ^ d := by
      calc
        (Real.sqrt (2 * Real.pi)) ^ d * (Real.sqrt (2 * Real.pi)) ^ d =
            (Real.sqrt (2 * Real.pi)) ^ (d + d) := (pow_add _ _ _).symm
        _ = (Real.sqrt (2 * Real.pi)) ^ (2 * d) := by congr 1; omega
        _ = ((Real.sqrt (2 * Real.pi)) ^ 2) ^ d := by rw [pow_mul]
    calc
      (Real.sqrt (2 * Real.pi)) ^ (2 * j + d) * (Real.sqrt (2 * Real.pi)) ^ d =
          (Real.sqrt (2 * Real.pi)) ^ (2 * j) *
            ((Real.sqrt (2 * Real.pi)) ^ d * (Real.sqrt (2 * Real.pi)) ^ d) := by
        rw [pow_add]
        ring
      _ = ((Real.sqrt (2 * Real.pi)) ^ 2) ^ j *
            ((Real.sqrt (2 * Real.pi)) ^ 2) ^ d := by rw [hleft, hright]
      _ = ((Real.sqrt (2 * Real.pi)) ^ 2) ^ (j + d) := by rw [pow_add]
      _ = (2 * Real.pi) ^ (j + d) := by rw [hsquare]
  have hfour : (2 * Real.pi) ^ (j + d) * (2 : Real) ^ (j + d) =
      (4 * Real.pi) ^ (j + d) := by
    calc
      (2 * Real.pi) ^ (j + d) * (2 : Real) ^ (j + d) =
          ((2 * Real.pi) * 2) ^ (j + d) := (mul_pow _ _ _).symm
      _ = (4 * Real.pi) ^ (j + d) := by congr 1; ring
  have hlast : (4 * Real.pi) ^ d *
      (((d + 1 : Nat) : Real) * Real.exp (-1) / Real.pi) ^ ((d : Real) / 2) =
      (16 * Real.pi * ((d + 1 : Nat) : Real) * Real.exp (-1)) ^ ((d : Real) / 2) := by
    have ha : 0 ≤ (4 * Real.pi : Real) := by positivity
    have hB : 0 ≤ ((d + 1 : Nat) : Real) * Real.exp (-1) / Real.pi := by positivity
    have hpow : (4 * Real.pi : Real) ^ d =
        ((4 * Real.pi : Real) ^ 2) ^ ((d : Real) / 2) := by
      calc
        (4 * Real.pi : Real) ^ d = (4 * Real.pi : Real) ^ (d : Real) :=
          (Real.rpow_natCast (4 * Real.pi) d).symm
        _ = (4 * Real.pi : Real) ^ ((2 : Real) * ((d : Real) / 2)) := by congr 1; ring
        _ = ((4 * Real.pi : Real) ^ 2) ^ ((d : Real) / 2) := by
          simpa using (Real.rpow_mul ha (2 : Real) ((d : Real) / 2))
    calc
      (4 * Real.pi) ^ d *
          (((d + 1 : Nat) : Real) * Real.exp (-1) / Real.pi) ^ ((d : Real) / 2) =
          ((4 * Real.pi : Real) ^ 2) ^ ((d : Real) / 2) *
            (((d + 1 : Nat) : Real) * Real.exp (-1) / Real.pi) ^ ((d : Real) / 2) := by rw [hpow]
      _ = (((4 * Real.pi : Real) ^ 2) *
            (((d + 1 : Nat) : Real) * Real.exp (-1) / Real.pi)) ^ ((d : Real) / 2) :=
        (Real.mul_rpow (by positivity) hB).symm
      _ = (16 * Real.pi * ((d + 1 : Nat) : Real) * Real.exp (-1)) ^ ((d : Real) / 2) := by
        congr 1
        field_simp [Real.pi_ne_zero]
        ring
  have hfactor :
      (Real.sqrt (2 * Real.pi)) ^ (2 * j + d) *
        ((2 : Real) ^ (j + d) * ((2 * j + d : Nat) : Real) ^ j) *
        (Real.sqrt (2 * Real.pi)) ^ d *
        (((d + 1 : Nat) : Real) * Real.exp (-1) / Real.pi) ^ ((d : Real) / 2) =
      (4 * Real.pi * ((2 * j + d : Nat) : Real)) ^ j *
        (16 * Real.pi * ((d + 1 : Nat) : Real) * Real.exp (-1)) ^ ((d : Real) / 2) := by
    calc
      (Real.sqrt (2 * Real.pi)) ^ (2 * j + d) *
          ((2 : Real) ^ (j + d) * ((2 * j + d : Nat) : Real) ^ j) *
          (Real.sqrt (2 * Real.pi)) ^ d *
          (((d + 1 : Nat) : Real) * Real.exp (-1) / Real.pi) ^ ((d : Real) / 2) =
          ((Real.sqrt (2 * Real.pi)) ^ (2 * j + d) *
            (Real.sqrt (2 * Real.pi)) ^ d) *
            ((2 : Real) ^ (j + d) * ((2 * j + d : Nat) : Real) ^ j) *
            (((d + 1 : Nat) : Real) * Real.exp (-1) / Real.pi) ^ ((d : Real) / 2) := by ring
      _ = (2 * Real.pi) ^ (j + d) * (2 : Real) ^ (j + d) *
            ((2 * j + d : Nat) : Real) ^ j *
            (((d + 1 : Nat) : Real) * Real.exp (-1) / Real.pi) ^ ((d : Real) / 2) := by
        rw [hsd]
        ring
      _ = (4 * Real.pi) ^ (j + d) * ((2 * j + d : Nat) : Real) ^ j *
            (((d + 1 : Nat) : Real) * Real.exp (-1) / Real.pi) ^ ((d : Real) / 2) := by rw [hfour]
      _ = (4 * Real.pi) ^ j * (4 * Real.pi) ^ d *
            ((2 * j + d : Nat) : Real) ^ j *
            (((d + 1 : Nat) : Real) * Real.exp (-1) / Real.pi) ^ ((d : Real) / 2) := by rw [pow_add]
      _ = (4 * Real.pi * ((2 * j + d : Nat) : Real)) ^ j *
            ((4 * Real.pi) ^ d *
              (((d + 1 : Nat) : Real) * Real.exp (-1) / Real.pi) ^ ((d : Real) / 2)) := by
            rw [mul_pow]
            ring
      _ = (4 * Real.pi * ((2 * j + d : Nat) : Real)) ^ j *
            (16 * Real.pi * ((d + 1 : Nat) : Real) * Real.exp (-1)) ^ ((d : Real) / 2) := by
        rw [hlast]
  have hpi4 : Real.pi ≤ 4 := by
    exact (le_of_lt Real.pi_lt_d2).trans (by norm_num)
  have hbaseJ : 4 * Real.pi * ((2 * j + d : Nat) : Real) ≤
      19 * ((2 * j + d + 1 : Nat) : Real) := by
    have hc4 : 4 * Real.pi ≤ (16 : Real) := by nlinarith
    have hstep : 4 * Real.pi * ((2 * j + d : Nat) : Real) ≤
        16 * ((2 * j + d : Nat) : Real) :=
      mul_le_mul_of_nonneg_right hc4 (Nat.cast_nonneg _)
    have hn : (0 : Real) ≤ ((2 * j + d : Nat) : Real) := Nat.cast_nonneg _
    push_cast
    nlinarith
  have hconst : 16 * Real.pi * Real.exp (-1) ≤ (19 : Real) := by
    have hprod : Real.pi * Real.exp (-1) ≤
        (3.1416 : Real) * (0.3678794412 : Real) := by
      exact mul_le_mul (le_of_lt Real.pi_lt_d4) (le_of_lt Real.exp_neg_one_lt_d9)
        (Real.exp_pos _).le (by norm_num)
    nlinarith
  have hnumNat : d + 1 ≤ 2 * j + d + 1 := by omega
  have hnum : ((d + 1 : Nat) : Real) ≤ ((2 * j + d + 1 : Nat) : Real) := by
    exact_mod_cast hnumNat
  have hbaseD : 16 * Real.pi * ((d + 1 : Nat) : Real) * Real.exp (-1) ≤
      19 * ((2 * j + d + 1 : Nat) : Real) := by
    calc
      16 * Real.pi * ((d + 1 : Nat) : Real) * Real.exp (-1) =
          (16 * Real.pi * Real.exp (-1)) * ((d + 1 : Nat) : Real) := by ring
      _ ≤ 19 * ((d + 1 : Nat) : Real) :=
        mul_le_mul_of_nonneg_right hconst (by positivity)
      _ ≤ 19 * ((2 * j + d + 1 : Nat) : Real) :=
        mul_le_mul_of_nonneg_left hnum (by norm_num)
  have hJ : (4 * Real.pi * ((2 * j + d : Nat) : Real)) ^ j ≤
      (19 * ((2 * j + d + 1 : Nat) : Real)) ^ j := by gcongr
  have hD : (16 * Real.pi * ((d + 1 : Nat) : Real) * Real.exp (-1)) ^ ((d : Real) / 2) ≤
      (19 * ((2 * j + d + 1 : Nat) : Real)) ^ ((d : Real) / 2) :=
    Real.rpow_le_rpow (by positivity) hbaseD (by positivity)
  let A : Real := 19 * ((2 * j + d + 1 : Nat) : Real)
  have hA : 0 < A := by dsimp [A]; positivity
  have hcast : A ^ j = A ^ (j : Real) := (Real.rpow_natCast A j).symm
  calc
    (Real.sqrt (2 * Real.pi)) ^ (2 * j + d) *
        ((2 : Real) ^ (j + d) * ((2 * j + d : Nat) : Real) ^ j) *
        (Real.sqrt (2 * Real.pi)) ^ d *
        (((d + 1 : Nat) : Real) * Real.exp (-1) / Real.pi) ^ ((d : Real) / 2) =
      (4 * Real.pi * ((2 * j + d : Nat) : Real)) ^ j *
        (16 * Real.pi * ((d + 1 : Nat) : Real) * Real.exp (-1)) ^ ((d : Real) / 2) := hfactor
    _ ≤ (19 * ((2 * j + d + 1 : Nat) : Real)) ^ j *
          (19 * ((2 * j + d + 1 : Nat) : Real)) ^ ((d : Real) / 2) :=
      mul_le_mul hJ hD (by positivity) (by positivity)
    _ = A ^ (j : Real) * A ^ ((d : Real) / 2) := by
      dsimp [A]
      rw [hcast]
    _ = A ^ ((j : Real) + (d : Real) / 2) :=
      (Real.rpow_add hA _ _).symm
    _ = (19 * ((2 * j + d + 1 : Nat) : Real)) ^
          (((2 * j + d : Nat) : Real) / 2) := by
      dsimp [A]
      congr 1
      push_cast
      ring
end Auto
