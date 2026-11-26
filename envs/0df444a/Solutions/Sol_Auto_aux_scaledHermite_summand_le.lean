-- Prove2me | solution 1 for Auto.aux_scaledHermite_summand_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:57:02.708828+00:00
-- url     : https://prove2.me/submissions/1cd58a68-582a-46c6-9ee6-01de82bd6f07

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
public import Theorems.Thm_Auto_aux_hermiteCoeff_bound
public import Theorems.Thm_Auto_aux_scaledHermite_term_le

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (m d : ℕ) (x : ℝ) (hd : d ≤ m) (he : Even (m + d)) :
    |(Real.sqrt (2 * Real.pi)) ^ m *
        (((Polynomial.hermite m).coeff d : ℝ) *
          (Real.sqrt (2 * Real.pi) * x) ^ d) *
        Real.exp (-((Real.sqrt (2 * Real.pi) * x) ^ 2 / 2))| ≤
      (19 * ((m + 1 : ℕ) : ℝ)) ^ ((m : ℝ) / 2) *
        Real.exp (-(Real.pi / 2) * x ^ 2) := by
  let s : ℝ := Real.sqrt (2 * Real.pi)
  let E : ℝ := Real.exp (-(Real.pi / 2) * x ^ 2)
  let B : ℝ := (((d + 1 : ℕ) : ℝ) * Real.exp (-1) / Real.pi) ^ ((d : ℝ) / 2)
  let j : ℕ := (m - d) / 2
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hE : 0 < E := by
    dsimp [E]
    positivity
  have hsubEven : Even (m - d) := by
    exact (Nat.even_sub hd).mpr ((Nat.even_add).mp he)
  have htwice : 2 * ((m - d) / 2) = m - d :=
    Nat.two_mul_div_two_of_even hsubEven
  have hm : m = 2 * j + d := by
    dsimp [j]
    omega
  have hp : m - (m - d) / 2 = j + d := by
    dsimp [j]
    omega
  have hcoeff := aux_hermiteCoeff_bound m d hd he
  have hcoeff' : |((Polynomial.hermite m).coeff d : ℝ)| ≤
      (2 : ℝ) ^ (j + d) * (m : ℝ) ^ j := by
    rw [← hp]
    exact hcoeff
  have habs := aux_abs_pow_mul_exp_neg_half_le d x
  have habs' : |x| ^ d * E ≤ B := by
    change |x| ^ d * Real.exp (-(Real.pi / 2) * x ^ 2) ≤
      (((d + 1 : ℕ) : ℝ) * Real.exp (-1) / Real.pi) ^ ((d : ℝ) / 2)
    exact habs
  have hcore := aux_scaledHermite_term_le m j d hm
  have hinner : s ^ m * |((Polynomial.hermite m).coeff d : ℝ)| * s ^ d *
      (|x| ^ d * E) ≤ (19 * ((m + 1 : ℕ) : ℝ)) ^ ((m : ℝ) / 2) := by
    calc
      s ^ m * |((Polynomial.hermite m).coeff d : ℝ)| * s ^ d * (|x| ^ d * E) ≤
          s ^ m * ((2 : ℝ) ^ (j + d) * (m : ℝ) ^ j) * s ^ d * (|x| ^ d * E) := by
            gcongr
      _ ≤ s ^ m * ((2 : ℝ) ^ (j + d) * (m : ℝ) ^ j) * s ^ d * B := by
            gcongr
      _ = (Real.sqrt (2 * Real.pi)) ^ m * ((2 : ℝ) ^ (j + d) * (m : ℝ) ^ j) *
          (Real.sqrt (2 * Real.pi)) ^ d *
          (((d + 1 : ℕ) : ℝ) * Real.exp (-1) / Real.pi) ^ ((d : ℝ) / 2) := by
            rfl
      _ ≤ (19 * ((m + 1 : ℕ) : ℝ)) ^ ((m : ℝ) / 2) := hcore
  have hexp : Real.exp (-((s * x) ^ 2 / 2)) = E * E := by
    rw [← Real.exp_add]
    dsimp [s, E]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    congr 1
    ring
  change |s ^ m * (((Polynomial.hermite m).coeff d : ℝ) * (s * x) ^ d) *
      Real.exp (-((s * x) ^ 2 / 2))| ≤
      (19 * ((m + 1 : ℕ) : ℝ)) ^ ((m : ℝ) / 2) * E
  calc
    |s ^ m * (((Polynomial.hermite m).coeff d : ℝ) * (s * x) ^ d) *
        Real.exp (-((s * x) ^ 2 / 2))| =
        (s ^ m * |((Polynomial.hermite m).coeff d : ℝ)| * s ^ d *
          (|x| ^ d * E)) * E := by
            rw [hexp]
            simp only [abs_mul, abs_pow, abs_of_pos hs, abs_of_pos hE]
            ring
    _ ≤ (19 * ((m + 1 : ℕ) : ℝ)) ^ ((m : ℝ) / 2) * E := by
      gcongr
end Auto
