-- Prove2me | solution 1 for Auto.aux_pow_mul_exp_neg_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:54:01.168326+00:00
-- url     : https://prove2.me/submissions/11c92ff6-cd36-4f5a-b019-b9087c816784

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
theorem _root_.solution (n : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    y ^ n * Real.exp (-y) ≤ ((n : ℝ) * Real.exp (-1)) ^ n := by
  by_cases hn : n = 0
  · subst hn
    simpa using (Real.exp_le_one_iff.mpr (by linarith : -y ≤ 0))
  · have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    have hbase := Real.mul_exp_neg_le_exp_neg_one (y / (n : ℝ))
    have hleft_nonneg : 0 ≤ y / (n : ℝ) * Real.exp (-(y / (n : ℝ))) := by
      positivity
    have hpow : (y / (n : ℝ) * Real.exp (-(y / (n : ℝ)))) ^ n ≤
        Real.exp (-1) ^ n := by
      gcongr
    have hpow' : (y / (n : ℝ)) ^ n * Real.exp (-y) ≤ Real.exp (-1) ^ n := by
      calc
        (y / (n : ℝ)) ^ n * Real.exp (-y) =
            (y / (n : ℝ) * Real.exp (-(y / (n : ℝ)))) ^ n := by
          rw [mul_pow, ← Real.exp_nat_mul]
          congr 1
          field_simp
        _ ≤ Real.exp (-1) ^ n := hpow
    calc
      y ^ n * Real.exp (-y) = (n : ℝ) ^ n *
          ((y / (n : ℝ)) ^ n * Real.exp (-y)) := by
        rw [div_pow]
        field_simp
      _ ≤ (n : ℝ) ^ n * Real.exp (-1) ^ n :=
        mul_le_mul_of_nonneg_left hpow' (pow_nonneg hnpos.le _)
      _ = ((n : ℝ) * Real.exp (-1)) ^ n := by rw [mul_pow]
end Auto
