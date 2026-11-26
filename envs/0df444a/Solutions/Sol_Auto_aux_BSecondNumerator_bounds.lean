-- Prove2me | solution 1 for Auto.aux_BSecondNumerator_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:48:27.483472+00:00
-- url     : https://prove2.me/submissions/bb66ba01-e1be-4b5c-8153-545b91996093

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
public import Theorems.Thm_Auto_aux_one_sub_gaussian_nonneg

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution {x : ℝ} (hx : |x| ≤ 1 / 2) :
    0 ≤ aux_BSecondNumerator x ∧
      aux_BSecondNumerator x ≤ 2 * (Real.pi * x ^ 2) ^ 2 := by
  let u : ℝ := Real.pi * x ^ 2
  let t : ℝ := 1 - gaussian x
  have hx2 : x ^ 2 ≤ 1 / 4 := by
    have h : |x| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg x) (by norm_num)).2 hx
    rw [sq_abs] at h
    norm_num at h ⊢
    exact h
  have hu0 : 0 ≤ u := by
    dsimp [u]
    positivity
  have hu1 : u ≤ 1 := by
    calc
      u ≤ 4 * x ^ 2 := by
        dsimp [u]
        exact mul_le_mul_of_nonneg_right Real.pi_le_four (sq_nonneg x)
      _ ≤ 4 * (1 / 4) := mul_le_mul_of_nonneg_left hx2 (by norm_num)
      _ = 1 := by norm_num
  have ht0 : 0 ≤ t := by
    simpa [t] using aux_one_sub_gaussian_nonneg x
  have hgauss : gaussian x = Real.exp (-u) := by
    simp [u, gaussian, Auto.gaussian]
  have ht_le_u : t ≤ u := by
    dsimp [t]
    rw [hgauss]
    have h : 1 - u ≤ Real.exp (-u) := by
      have h' := Real.add_one_le_exp (-u)
      linarith
    linarith
  have hdenpos : 0 < 1 + u := by linarith
  have hexp : 1 + u ≤ Real.exp u := by
    simpa [add_comm] using Real.add_one_le_exp u
  have hinv : Real.exp (-u) ≤ (1 + u)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos u) hdenpos).2 hexp
  have ht_lower : u / (1 + u) ≤ t := by
    dsimp [t]
    rw [hgauss]
    have hfrac : u / (1 + u) = 1 - (1 + u)⁻¹ := by
      field_simp
      ring
    rw [hfrac]
    linarith
  have hsub : u - t ≤ u ^ 2 := by
    calc
      u - t ≤ u - u / (1 + u) := sub_le_sub_left ht_lower u
      _ = u ^ 2 / (1 + u) := by
        field_simp
        ring
      _ ≤ u ^ 2 := (div_le_iff₀ hdenpos).2 (by nlinarith [sq_nonneg u])
  have hrest : (1 - u) * t ^ 2 ≤ u ^ 2 := by
    have htsq : t ^ 2 ≤ u ^ 2 := (sq_le_sq₀ ht0 hu0).2 ht_le_u
    calc
      (1 - u) * t ^ 2 ≤ 1 * t ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg t)
      _ ≤ 1 * u ^ 2 := mul_le_mul_of_nonneg_left htsq zero_le_one
      _ = u ^ 2 := by ring
  change 0 ≤ u - t + (1 - u) * t ^ 2 ∧
    u - t + (1 - u) * t ^ 2 ≤ 2 * u ^ 2
  constructor
  · exact add_nonneg (sub_nonneg.mpr ht_le_u)
      (mul_nonneg (by linarith) (sq_nonneg t))
  · linarith
end Auto
