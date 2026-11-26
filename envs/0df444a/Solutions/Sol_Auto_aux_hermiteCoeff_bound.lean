-- Prove2me | solution 1 for Auto.aux_hermiteCoeff_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:56:08.8356+00:00
-- url     : https://prove2.me/submissions/0364bbad-e992-49d0-b5e6-0867a1c2d12b

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
public import Theorems.Thm_Auto_aux_hermiteCoeff_nat_bound

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (m d : ℕ) (hd : d ≤ m) (he : Even (m + d)) :
    |((Polynomial.hermite m).coeff d : ℝ)| ≤
      (2 : ℝ) ^ (m - (m - d) / 2) * (m : ℝ) ^ ((m - d) / 2) := by
  have hsubEven : Even (m - d) := by
    exact (Nat.even_sub hd).mpr ((Nat.even_add).mp he)
  have htwice : 2 * ((m - d) / 2) = m - d :=
    Nat.two_mul_div_two_of_even hsubEven
  let j : ℕ := (m - d) / 2
  have hm : m = 2 * j + d := by
    dsimp [j]
    omega
  have hnat := aux_hermiteCoeff_nat_bound j d
  have hnat' : (m - d - 1).doubleFactorial * m.choose d ≤
      2 ^ (m - (m - d) / 2) * m ^ ((m - d) / 2) := by
    rw [hm]
    have hsub : 2 * j + d - d = 2 * j := by omega
    rw [hsub]
    have hj : 2 * j / 2 = j := by omega
    have hpow : 2 * j + d - j = j + d := by omega
    rw [hj, hpow]
    exact hnat
  have hcast : ((m - d - 1).doubleFactorial : ℝ) * (m.choose d : ℝ) ≤
      (2 : ℝ) ^ (m - (m - d) / 2) * (m : ℝ) ^ ((m - d) / 2) := by
    exact_mod_cast hnat'
  calc
    |((Polynomial.hermite m).coeff d : ℝ)| =
        ((m - d - 1).doubleFactorial : ℝ) * (m.choose d : ℝ) := by
      rw [Polynomial.coeff_hermite, if_pos he]
      push_cast
      rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    _ ≤ (2 : ℝ) ^ (m - (m - d) / 2) * (m : ℝ) ^ ((m - d) / 2) := hcast
end Auto
