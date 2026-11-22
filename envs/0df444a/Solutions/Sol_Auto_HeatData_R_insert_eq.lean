-- Prove2me | solution 1 for Auto.HeatData.R_insert_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:34:53.368843+00:00
-- url     : https://prove2.me/submissions/f85696ff-f711-4f80-bfe4-aa3fac610dd6

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_rdiag_mul_rdiag
public import Theorems.Thm_Auto_HeatData_rdiag_conjTranspose
public import Theorems.Thm_Auto_HeatData_sq_mul_sq
public import Theorems.Thm_Auto_HeatData_R_eq

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
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Auto.HeatData
variable (Hd : HeatData ι)
namespace Auto.HeatData
theorem _root_.solution (hh : 0 ≤ Hd.h) (p σ : Fin 3 → ℝ) (v : Fin 3) (D : ι → ℝ) (hσ : 0 < σ v) :
    (Hd.R p σ v)ᴴ * rdiag D * Hd.R p σ v = wGram (Hd.Brow p σ v) (fun i => Hd.w p σ v i * D i) := by
  rw [R_eq, wGram, Brow]
  have hw : (fun i => Hd.w p σ v i * D i) = Hd.sqw p σ v * D * Hd.sqw p σ v := by
    funext i
    simp only [Pi.mul_apply]
    rw [← Hd.sq_mul_sq p σ hh hσ]; simp only [Pi.mul_apply]; ring
  rw [hw, ← rdiag_mul_rdiag, ← rdiag_mul_rdiag]
  simp only [Matrix.conjTranspose_mul, rdiag_conjTranspose, Matrix.mul_assoc]
end Auto.HeatData
