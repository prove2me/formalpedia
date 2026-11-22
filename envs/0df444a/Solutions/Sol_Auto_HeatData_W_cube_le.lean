-- Prove2me | solution 1 for Auto.HeatData.W_cube_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:29:45.74443+00:00
-- url     : https://prove2.me/submissions/2ad57a91-416f-4af2-97a5-bd91f590934c

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_P2M_Auto_gweight_nonneg__bb3decd414c3
public import Theorems.Thm_Auto_HeatData_rdiag_mul_mul_rdiag_apply
public import Theorems.Thm_Auto_holder_three_halves

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Auto.HeatData
variable (Hd : HeatData ι)
namespace Auto.HeatData
theorem _root_.solution (hh : 0 ≤ Hd.h) (p σ : Fin 3 → ℝ) (v : Fin 3) {M : ℝ} (hM : 0 ≤ M)
    (h1 : ∑ i, Hd.w p σ v i ≤ M) (h2 : ∑ j, Hd.w p σ (v + 1) j ≤ M) :
    hsSq (Hd.W p σ v) ^ (3 / 2 : ℝ) ≤ M * ∑ i, ∑ j, ‖Hd.A v i j‖ ^ 3 * Hd.w p σ v i * Hd.w p σ
      (v + 1) j := by
  set w := Hd.w p σ v
  set w' := Hd.w p σ (v + 1)
  have hw : ∀ i, 0 ≤ w i := fun i => gweight_nonneg' _ hh _ _ i
  have hw' : ∀ j, 0 ≤ w' j := fun j => gweight_nonneg' _ hh _ _ j
  have hsq : ∀ k i, Hd.sqw p σ k i ^ 2 = Hd.w p σ k i := fun k i =>
    Real.sq_sqrt (gweight_nonneg' _ hh _ _ i)
  have hW : hsSq (Hd.W p σ v) = ∑ z : ι × ι, (w z.1 * w' z.2) * ‖Hd.A v z.1 z.2‖ ^ 2 := by
    rw [hsSq, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [W, rdiag_mul_mul_rdiag_apply, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs, hsq, hsq]
    ring
  have hH := holder_three_halves Finset.univ (fun z : ι × ι => w z.1 * w' z.2) (fun z => ‖Hd.A v z.1
      z.2‖ ^ 2) (fun z => mul_nonneg (hw _) (hw' _)) (fun z => sq_nonneg _)
  rw [← hW] at hH
  have hQ : ∑ z : ι × ι, w z.1 * w' z.2 = (∑ i, w i) * (∑ j, w' j) := by
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  have hQM : (∑ z : ι × ι, w z.1 * w' z.2) ^ (1 / 2 : ℝ) ≤ M := by
    rw [hQ, ← Real.sqrt_eq_rpow, Real.sqrt_le_left hM]
    have a1 : 0 ≤ ∑ i, w i := Finset.sum_nonneg fun i _ => hw i
    have a2 : 0 ≤ ∑ j, w' j := Finset.sum_nonneg fun j _ => hw' j
    nlinarith [mul_le_mul h1 h2 a2 hM]
  have hpow : ∀ z : ι × ι, (‖Hd.A v z.1 z.2‖ ^ 2) ^ (3 / 2 : ℝ) = ‖Hd.A v z.1 z.2‖ ^ 3 := by
    intro z
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  simp only [hpow] at hH
  have hS : 0 ≤ ∑ z : ι × ι, w z.1 * w' z.2 * ‖Hd.A v z.1 z.2‖ ^ 3 :=
    Finset.sum_nonneg fun z _ => by have := hw z.1; have := hw' z.2; positivity
  calc hsSq (Hd.W p σ v) ^ (3 / 2 : ℝ)
      ≤ (∑ z : ι × ι, w z.1 * w' z.2) ^ (1 / 2 : ℝ) *
          ∑ z : ι × ι, w z.1 * w' z.2 * ‖Hd.A v z.1 z.2‖ ^ 3 := hH
    _ ≤ M * ∑ z : ι × ι, w z.1 * w' z.2 * ‖Hd.A v z.1 z.2‖ ^ 3 := by gcongr
    _ = _ := by
      rw [Fintype.sum_prod_type]
      congr 1
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
end Auto.HeatData
