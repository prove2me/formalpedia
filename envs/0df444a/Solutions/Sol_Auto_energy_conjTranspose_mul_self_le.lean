-- Prove2me | solution 1 for Auto.energy_conjTranspose_mul_self_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:04:29.293527+00:00
-- url     : https://prove2.me/submissions/446d0713-f1b8-4956-be4f-acb09b902455

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_trF_eq_sum

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Auto
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
omit [DecidableEq m]
namespace Auto
theorem _root_.solution (R : Matrix m n ℂ) :
    energy (Rᴴ * R) ≤ hsSq R ^ (3 / 2 : ℝ) := by
  have h1 : (Rᴴ * R).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self R
  have hnn : ∀ i, 0 ≤ h1.eigenvalues i :=
    fun i => Matrix.eigenvalues_conjTranspose_mul_self_nonneg R i
  have htr : ∑ i, h1.eigenvalues i = hsSq R := by
    have := h1.trace_eq_sum_eigenvalues
    rw [← re_trace_conjTranspose_mul_self, this]
    simp
  rw [energy, trF_eq_sum _ h1, ← htr]
  set S := ∑ i, h1.eigenvalues i
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => hnn i
  calc ∑ i, h1.eigenvalues i ^ (3 / 2 : ℝ) ≤ ∑ i, h1.eigenvalues i * S ^ (1 / 2 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' (hnn i) (by norm_num),
          Real.rpow_one]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hnn i) (Finset.single_le_sum (fun j _ =>
            hnn j) (Finset.mem_univ i)) (by norm_num)) (hnn i)
    _ = S ^ (3 / 2 : ℝ) := by
        rw [← Finset.sum_mul, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
          Real.rpow_add' hS (by norm_num), Real.rpow_one]
end Auto
