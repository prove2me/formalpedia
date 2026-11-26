-- Prove2me | solution 1 for Auto.aux_halfCard_le_rpow_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:54:11.921049+00:00
-- url     : https://prove2.me/submissions/86902266-e03d-4314-915f-06a39f6c2f3b

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
theorem _root_.solution (m : ℕ) :
    ((m / 2 + 1 : ℕ) : ℝ) ≤ Real.rpow 2 ((m : ℝ) / 2) := by
  have hsucc : ∀ k : ℕ, k + 1 ≤ 2 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        k + 1 + 1 ≤ 2 * (k + 1) := by omega
        _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (k + 1) := by simp [pow_succ, Nat.mul_comm]
  have hcast : ((m / 2 + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (m / 2) := by
    exact_mod_cast hsucc (m / 2)
  have hdivNat : 2 * (m / 2) ≤ m := Nat.mul_div_le m 2
  have hdiv : (2 : ℝ) * ((m / 2 : ℕ) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hdivNat
  calc
    ((m / 2 + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (m / 2) := hcast
    _ = Real.rpow 2 ((m / 2 : ℕ) : ℝ) := (Real.rpow_natCast 2 (m / 2)).symm
    _ ≤ Real.rpow 2 ((m : ℝ) / 2) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith
end Auto
