-- Prove2me | solution 1 for Auto.aux_hermiteCoeff_nat_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:55:01.808441+00:00
-- url     : https://prove2.me/submissions/ea9ce117-35bc-4e1a-8e69-a78e4e79627b

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
public import Theorems.Thm_Auto_aux_oddDoubleFactorial_mul_twoPow_mul_factorial

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (j d : ℕ) :
    Nat.doubleFactorial (2 * j - 1) * Nat.choose (2 * j + d) d ≤
      2 ^ (j + d) * (2 * j + d) ^ j := by
  apply Nat.le_of_mul_le_mul_right (c := 2 ^ j * j.factorial * d.factorial) ?_
    (by positivity)
  have hchoose : Nat.choose (2 * j + d) d ≤ 2 ^ (2 * j + d) :=
    Nat.choose_le_two_pow _ _
  have hpow : (2 * j) ^ j ≤ (2 * j + d) ^ j :=
    Nat.pow_le_pow_left (by omega) _
  have hfact : (2 * j).factorial ≤ (2 * j + d) ^ j * j.factorial := by
    calc
      (2 * j).factorial ≤ (2 * j) ^ j * j.factorial := Nat.factorial_two_mul_le j
      _ ≤ (2 * j + d) ^ j * j.factorial := Nat.mul_le_mul_right _ hpow
  have hchooseFact :=
    Nat.choose_mul_factorial_mul_factorial (n := 2 * j + d) (k := d) (by omega)
  have hsub : 2 * j + d - d = 2 * j := by omega
  rw [hsub] at hchooseFact
  calc
    (Nat.doubleFactorial (2 * j - 1) * Nat.choose (2 * j + d) d) *
        (2 ^ j * j.factorial * d.factorial) =
        Nat.choose (2 * j + d) d * d.factorial *
          (Nat.doubleFactorial (2 * j - 1) * (2 ^ j * j.factorial)) := by ring
    _ = Nat.choose (2 * j + d) d * d.factorial * (2 * j).factorial := by
      rw [aux_oddDoubleFactorial_mul_twoPow_mul_factorial]
    _ = (2 * j + d).factorial := hchooseFact
    _ ≤ (2 ^ (2 * j + d) * d.factorial) * ((2 * j + d) ^ j * j.factorial) := by
      rw [← hchooseFact]
      exact Nat.mul_le_mul (Nat.mul_le_mul_right _ hchoose) hfact
    _ = (2 ^ (j + d) * (2 * j + d) ^ j) *
        (2 ^ j * j.factorial * d.factorial) := by
          rw [show 2 * j + d = (j + d) + j by omega, pow_add]
          ring
end Auto
