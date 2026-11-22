-- Prove2me | solution 1 for Auto.gridGaussianForm_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:45:41.261171+00:00
-- url     : https://prove2.me/submissions/4bad0e1c-263e-4b2b-99a7-e404cb8ac79d

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_eq_zero_of_nNorm_eq_zero
public import Theorems.Thm_Auto_heatBoundConstant_nonneg
public import Theorems.Thm_Auto_gridGaussianForm_cubic_bound
public import Theorems.Thm_Auto_nNorm_cube
public import Theorems.Thm_Auto_gridGaussianForm_scale
public import Theorems.Thm_Auto_nCube_scale

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
public section
open Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace Auto
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Hd : HeatData ι) {kk : ι → ℤ} (hk : Function.Injective kk)
    (hu : ∀ i, Hd.u i = Hd.h * kk i) (hh : 0 < Hd.h)
    {a b : ℝ} (ha : Hd.h ^ 2 ≤ a) (hab : a ≤ b) :
    ‖gridGaussianForm Hd a b‖ ≤ 3 * heatBoundConstant *
      nNorm Hd.h (Hd.A 0) * nNorm Hd.h (Hd.A 1) * nNorm Hd.h (Hd.A 2) := by
  let N : Fin 3 → ℝ := fun v => nNorm Hd.h (Hd.A v)
  have hN0 : ∀ v, 0 ≤ N v := fun v => by dsimp [N, nNorm]; positivity
  by_cases hN : ∀ v, 0 < N v
  · let c : Fin 3 → ℂ := fun v => ((N v)⁻¹ : ℝ)
    let D := scaleHeatData Hd c
    have hD : ∀ v, D.nCube v = 1 := by
      intro v
      rw [show D.nCube v = ‖c v‖ ^ 3 * Hd.nCube v from nCube_scale Hd c v]
      have he : ‖c v‖ = (N v)⁻¹ := by
        simp only [c, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hN v))]
      rw [he, show Hd.nCube v = N v ^ 3 from (nNorm_cube Hd.h (Hd.A v)).symm]
      field_simp [(hN v).ne']
    have hb := gridGaussianForm_cubic_bound D hk hu hh ha hab
    simp only [hD, Fin.sum_univ_three] at hb
    rw [gridGaussianForm_scale, norm_mul, norm_mul, norm_mul] at hb
    have hc : ∀ v, ‖c v‖ = (N v)⁻¹ := fun v => by
      simp only [c, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hN v))]
    simp only [hc] at hb
    have hp : 0 < N 0 * N 1 * N 2 := mul_pos (mul_pos (hN 0) (hN 1)) (hN 2)
    have hb' : (N 0 * N 1 * N 2)⁻¹ * ‖gridGaussianForm Hd a b‖ ≤
        3 * heatBoundConstant := by
      simpa only [mul_inv, mul_comm heatBoundConstant 3, show (1 + 1 + 1 : ℝ) = 3 by norm_num]
        using hb
    calc
      ‖gridGaussianForm Hd a b‖ =
          (N 0 * N 1 * N 2) * ((N 0 * N 1 * N 2)⁻¹ * ‖gridGaussianForm Hd a b‖) := by
        rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
      _ ≤ (N 0 * N 1 * N 2) * (3 * heatBoundConstant) :=
        mul_le_mul_of_nonneg_left hb' hp.le
      _ = _ := by dsimp [N]; ring
  · push Not at hN
    obtain ⟨v, hv⟩ := hN
    have hz : N v = 0 := le_antisymm hv (hN0 v)
    have hA : Hd.A v = 0 := eq_zero_of_nNorm_eq_zero hh hz
    have hg : gridGaussianForm Hd a b = 0 := by
      fin_cases v
      · change Hd.A 0 = 0 at hA
        simp [gridGaussianForm, hA]
      · change Hd.A 1 = 0 at hA
        simp [gridGaussianForm, hA]
      · change Hd.A 2 = 0 at hA
        simp [gridGaussianForm, hA]
    rw [hg, norm_zero]
    have hC := heatBoundConstant_nonneg
    change 0 ≤ 3 * heatBoundConstant * N 0 * N 1 * N 2
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC)
      (hN0 0)) (hN0 1)) (hN0 2)
end Auto
