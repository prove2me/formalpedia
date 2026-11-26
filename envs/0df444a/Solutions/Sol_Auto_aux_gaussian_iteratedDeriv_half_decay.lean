-- Prove2me | solution 1 for Auto.aux_gaussian_iteratedDeriv_half_decay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:58:54.03288+00:00
-- url     : https://prove2.me/submissions/e30991ad-b414-4325-b76a-c8f3bab5b00f

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
public import Theorems.Thm_Auto_aux_gaussian_iteratedDeriv_hermite
public import Theorems.Thm_Auto_aux_hermiteParity_card_le
public import Theorems.Thm_Auto_aux_halfCard_le_rpow_two
public import Theorems.Thm_Auto_aux_scaledHermite_summand_le

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (m : ℕ) (x : ℝ) :
    |iteratedDeriv m gaussian x| ≤
      (38 * ((m + 1 : ℕ) : ℝ)) ^ ((m : ℝ) / 2) *
        Real.exp (-(Real.pi / 2) * x ^ 2) := by
  let s : ℝ := Real.sqrt (2 * Real.pi)
  let E : ℝ := Real.exp (-(Real.pi / 2) * x ^ 2)
  let R : ℝ := (19 * ((m + 1 : ℕ) : ℝ)) ^ ((m : ℝ) / 2)
  let S := (Finset.range (m + 1)).filter (fun d => Even (m + d))
  have hEval : Polynomial.aeval (s * x) (Polynomial.hermite m) =
      Finset.sum (Finset.range (m + 1))
        (fun d => ((Polynomial.hermite m).coeff d : ℝ) * (s * x) ^ d) := by
    rw [Polynomial.aeval_eq_sum_range, Polynomial.natDegree_hermite]
    simp [Algebra.smul_def]
  have hFilter : Finset.sum (Finset.range (m + 1))
        (fun d => ((Polynomial.hermite m).coeff d : ℝ) * (s * x) ^ d) =
      Finset.sum S
        (fun d => ((Polynomial.hermite m).coeff d : ℝ) * (s * x) ^ d) := by
    rw [show S = (Finset.range (m + 1)).filter (fun d => Even (m + d)) by rfl,
      Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases h : Even (m + d)
    · rw [if_pos h]
    · rw [Polynomial.coeff_hermite, if_neg h, if_neg h]
      simp
  have hterm : ∀ d ∈ S,
      |s ^ m * (((Polynomial.hermite m).coeff d : ℝ) * (s * x) ^ d) *
        Real.exp (-((s * x) ^ 2 / 2))| ≤ R * E := by
    intro d hd
    have hd' : d ∈ (Finset.range (m + 1)).filter (fun d => Even (m + d)) := by
      simpa only [S] using hd
    have hdle : d ≤ m := by
      have hdmem : d ∈ Finset.range (m + 1) :=
        (Finset.mem_filter.mp hd').1
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hdmem)
    have he : Even (m + d) :=
      (Finset.mem_filter.mp hd').2
    change |(Real.sqrt (2 * Real.pi)) ^ m *
        (((Polynomial.hermite m).coeff d : ℝ) *
          (Real.sqrt (2 * Real.pi) * x) ^ d) *
        Real.exp (-((Real.sqrt (2 * Real.pi) * x) ^ 2 / 2))| ≤
      (19 * ((m + 1 : ℕ) : ℝ)) ^ ((m : ℝ) / 2) *
        Real.exp (-(Real.pi / 2) * x ^ 2)
    exact aux_scaledHermite_summand_le m d x hdle he
  have hcardNat : S.card ≤ m / 2 + 1 := by
    simpa [S] using aux_hermiteParity_card_le m
  have hcard : (S.card : ℝ) ≤ Real.rpow 2 ((m : ℝ) / 2) := by
    calc
      (S.card : ℝ) ≤ ((m / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast hcardNat
      _ ≤ Real.rpow 2 ((m : ℝ) / 2) := aux_halfCard_le_rpow_two m
  have hcombine : Real.rpow 2 ((m : ℝ) / 2) * R =
      (38 * ((m + 1 : ℕ) : ℝ)) ^ ((m : ℝ) / 2) := by
    change Real.rpow 2 ((m : ℝ) / 2) *
        Real.rpow (19 * ((m + 1 : ℕ) : ℝ)) ((m : ℝ) / 2) = _
    calc
      Real.rpow 2 ((m : ℝ) / 2) *
          Real.rpow (19 * ((m + 1 : ℕ) : ℝ)) ((m : ℝ) / 2) =
          Real.rpow (2 * (19 * ((m + 1 : ℕ) : ℝ))) ((m : ℝ) / 2) :=
            (Real.mul_rpow (by norm_num) (by positivity)).symm
      _ = Real.rpow (38 * ((m + 1 : ℕ) : ℝ)) ((m : ℝ) / 2) := by
        congr 1
        ring
  rw [aux_gaussian_iteratedDeriv_hermite]
  change |s ^ m * ((-1 : ℝ) ^ m * Polynomial.aeval (s * x) (Polynomial.hermite m) *
      Real.exp (-((s * x) ^ 2 / 2)))| ≤
      (38 * ((m + 1 : ℕ) : ℝ)) ^ ((m : ℝ) / 2) * E
  rw [hEval, hFilter]
  have hsumEq : s ^ m * ((-1 : ℝ) ^ m * Finset.sum S
      (fun d => ((Polynomial.hermite m).coeff d : ℝ) * (s * x) ^ d) *
      Real.exp (-((s * x) ^ 2 / 2))) =
      (-1 : ℝ) ^ m * Finset.sum S (fun d =>
        s ^ m * (((Polynomial.hermite m).coeff d : ℝ) * (s * x) ^ d) *
          Real.exp (-((s * x) ^ 2 / 2))) := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  have hsign : |(-1 : ℝ) ^ m| = 1 := by
    rw [abs_pow, abs_neg, abs_one, one_pow]
  calc
    |s ^ m * ((-1 : ℝ) ^ m * Finset.sum S
        (fun d => ((Polynomial.hermite m).coeff d : ℝ) * (s * x) ^ d) *
        Real.exp (-((s * x) ^ 2 / 2)))| =
        |(-1 : ℝ) ^ m * Finset.sum S (fun d =>
          (s ^ m * (((Polynomial.hermite m).coeff d : ℝ) * (s * x) ^ d) *
            Real.exp (-((s * x) ^ 2 / 2))))| := by rw [hsumEq]
    _ = |Finset.sum S (fun d =>
          (s ^ m * (((Polynomial.hermite m).coeff d : ℝ) * (s * x) ^ d) *
            Real.exp (-((s * x) ^ 2 / 2))))| := by
      rw [abs_mul, hsign, one_mul]
    _ ≤ Finset.sum S (fun d => (|s ^ m *
          (((Polynomial.hermite m).coeff d : ℝ) * (s * x) ^ d) *
            Real.exp (-((s * x) ^ 2 / 2))|)) :=
      Finset.abs_sum_le_sum_abs _ S
    _ ≤ Finset.sum S (fun _ => R * E) := by
      apply Finset.sum_le_sum
      intro d hd
      exact hterm d hd
    _ = (S.card : ℝ) * (R * E) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Real.rpow 2 ((m : ℝ) / 2) * (R * E) := by
      gcongr
    _ = (38 * ((m + 1 : ℕ) : ℝ)) ^ ((m : ℝ) / 2) * E := by
      rw [show Real.rpow 2 ((m : ℝ) / 2) * (R * E) =
          (Real.rpow 2 ((m : ℝ) / 2) * R) * E by ring, hcombine]
end Auto
