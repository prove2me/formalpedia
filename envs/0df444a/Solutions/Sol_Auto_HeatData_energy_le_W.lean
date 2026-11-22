-- Prove2me | solution 1 for Auto.HeatData.energy_le_W
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:30:33.050116+00:00
-- url     : https://prove2.me/submissions/6ddc2a5e-150f-4714-9ad9-e31b11c3faf9

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_energyReg_zero
public import Theorems.Thm_Auto_energy_conjTranspose_mul_self_le
public import Theorems.Thm_Auto_holder_three_halves
public import Theorems.Thm_Auto_hsSq_fromCols
public import Theorems.Thm_Auto_hsSq_conjTranspose

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
theorem _root_.solution (p σ : Fin 3 → ℝ) (v : Fin 3) :
    Hd.e p σ 0 v ≤ √2 * (hsSq (Hd.W p σ v) ^ (3 / 2 : ℝ) + hsSq (Hd.W p σ (v - 1)) ^ (3 / 2 :
      ℝ)) := by
  have h1 : Hd.e p σ 0 v ≤ hsSq (Hd.R p σ v) ^ (3 / 2 : ℝ) := by
    rw [e, energyReg_zero, T]
    exact energy_conjTranspose_mul_self_le _
  have h2 : hsSq (Hd.R p σ v) = hsSq (Hd.W p σ v) + hsSq (Hd.W p σ (v - 1)) := by
    rw [R, rowMat, hsSq_fromCols, hsSq_conjTranspose]
  have h3 := holder_three_halves Finset.univ (fun _ : Fin 2 => (1 : ℝ))
    ![hsSq (Hd.W p σ v), hsSq (Hd.W p σ (v - 1))] (fun _ => zero_le_one)
    (fun k => by fin_cases k <;> exact hsSq_nonneg _)
  simp only [Fin.sum_univ_two, one_mul, Matrix.cons_val_zero, Matrix.cons_val_one] at h3
  rw [show (1 + 1 : ℝ) ^ (1 / 2 : ℝ) = √2 by rw [Real.sqrt_eq_rpow]; norm_num] at h3
  rw [h2] at h1
  exact h1.trans h3
end Auto.HeatData
