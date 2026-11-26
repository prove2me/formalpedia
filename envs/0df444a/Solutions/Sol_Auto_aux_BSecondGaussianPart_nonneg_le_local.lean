-- Prove2me | solution 1 for Auto.aux_BSecondGaussianPart_nonneg_le_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:58:56.752874+00:00
-- url     : https://prove2.me/submissions/a57bc97f-fe71-4f65-b3c1-9f56a40b1726

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
public import Theorems.Thm_Auto_aux_sqrtOneMinusGaussian_pos
public import Theorems.Thm_Auto_aux_sqrtOneMinusGaussian_lower
public import Theorems.Thm_Auto_aux_BSecondNumerator_bounds
public import Theorems.Thm_Auto_aux_BSecondGaussianPart_eq_cancelled

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution {x : ℝ}
    (hx0 : x ≠ 0) (hx : |x| ≤ 1 / 2) :
    0 ≤ ((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
          (2 * sqrtOneMinusGaussian x) +
        (-2 * Real.pi * x * gaussian x) ^ 2 /
          (4 * sqrtOneMinusGaussian x ^ 3) ∧
      ((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
          (2 * sqrtOneMinusGaussian x) +
        (-2 * Real.pi * x * gaussian x) ^ 2 /
          (4 * sqrtOneMinusGaussian x ^ 3) ≤
        2 * Real.pi * Real.sqrt Real.pi * |x| *
          Real.exp (3 * (Real.pi * x ^ 2) / 2) := by
  rw [aux_BSecondGaussianPart_eq_cancelled hx0]
  let u : ℝ := Real.pi * x ^ 2
  let L : ℝ := Real.sqrt Real.pi * |x| * Real.exp (-u / 2)
  let T : ℝ := 2 * Real.pi * Real.sqrt Real.pi * |x| *
    Real.exp (3 * u / 2)
  have hnum := aux_BSecondNumerator_bounds hx
  have hfpos : 0 < sqrtOneMinusGaussian x := aux_sqrtOneMinusGaussian_pos hx0
  have hL : L ≤ sqrtOneMinusGaussian x := by
    dsimp [L, u]
    convert aux_sqrtOneMinusGaussian_lower x using 1; ring_nf
  have hLpos : 0 < L := by
    dsimp [L]
    exact mul_pos (mul_pos (Real.sqrt_pos.2 Real.pi_pos) (abs_pos.mpr hx0))
      (Real.exp_pos _)
  have hTnonneg : 0 ≤ T := by
    dsimp [T]
    positivity
  have hnumscaled : Real.pi * aux_BSecondNumerator x ≤
      2 * Real.pi ^ 3 * x ^ 4 := by
    calc
      Real.pi * aux_BSecondNumerator x ≤ Real.pi * (2 * u ^ 2) :=
        mul_le_mul_of_nonneg_left hnum.2 Real.pi_pos.le
      _ = 2 * Real.pi ^ 3 * x ^ 4 := by
        dsimp [u]
        ring
  have hfcube : L ^ 3 ≤ sqrtOneMinusGaussian x ^ 3 :=
    pow_le_pow_left₀ hLpos.le hL 3
  have hsqrtsq : Real.sqrt Real.pi ^ 2 = Real.pi :=
    Real.sq_sqrt Real.pi_pos.le
  have hexp : Real.exp (3 * u / 2) * Real.exp (-u / 2) ^ 3 = 1 := by
    calc
      Real.exp (3 * u / 2) * Real.exp (-u / 2) ^ 3 =
          Real.exp (3 * u / 2) * Real.exp (3 * (-u / 2)) := by
          rw [← Real.exp_nat_mul]
          norm_num
      _ = Real.exp (3 * u / 2 + 3 * (-u / 2)) := by rw [← Real.exp_add]
      _ = 1 := by
        rw [show 3 * u / 2 + 3 * (-u / 2) = 0 by ring, Real.exp_zero]
  have hTL : T * L ^ 3 = 2 * Real.pi ^ 3 * x ^ 4 := by
    calc
      T * L ^ 3 = 2 * Real.pi * (Real.sqrt Real.pi) ^ 4 * |x| ^ 4 *
          (Real.exp (3 * u / 2) * Real.exp (-u / 2) ^ 3) := by
          dsimp [T, L]
          ring
      _ = 2 * Real.pi ^ 3 * x ^ 4 := by
        rw [hexp, show (Real.sqrt Real.pi) ^ 4 =
            (Real.sqrt Real.pi ^ 2) ^ 2 by ring, hsqrtsq,
          show |x| ^ 4 = (|x| ^ 2) ^ 2 by ring, sq_abs]
        ring
  have hcore : Real.pi * aux_BSecondNumerator x ≤
      T * sqrtOneMinusGaussian x ^ 3 := by
    calc
      Real.pi * aux_BSecondNumerator x ≤ 2 * Real.pi ^ 3 * x ^ 4 := hnumscaled
      _ = T * L ^ 3 := hTL.symm
      _ ≤ T * sqrtOneMinusGaussian x ^ 3 :=
        mul_le_mul_of_nonneg_left hfcube hTnonneg
  have hquot : Real.pi * aux_BSecondNumerator x /
      sqrtOneMinusGaussian x ^ 3 ≤ T :=
    (div_le_iff₀ (pow_pos hfpos 3)).2 hcore
  have hquotnonneg : 0 ≤ Real.pi * aux_BSecondNumerator x /
      sqrtOneMinusGaussian x ^ 3 :=
    div_nonneg (mul_nonneg Real.pi_pos.le hnum.1) (pow_nonneg hfpos.le _)
  constructor
  · exact hquotnonneg
  · simpa [T, u] using hquot
end Auto
