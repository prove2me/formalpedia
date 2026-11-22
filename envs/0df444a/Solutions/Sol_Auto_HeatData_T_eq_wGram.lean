-- Prove2me | solution 1 for Auto.HeatData.T_eq_wGram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:35:35.171065+00:00
-- url     : https://prove2.me/submissions/820c8c5f-b35e-4faf-aca6-b66965e296a2

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
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Auto.HeatData
variable (Hd : HeatData ι) (p σ : Fin 3 → ℝ)
namespace Auto.HeatData
theorem _root_.solution (hh : 0 ≤ Hd.h) {v : Fin 3} (hσ : 0 < σ v) :
    Hd.T p σ v = wGram (Hd.Brow p σ v) (Hd.w p σ v) := by
  rw [T, R_eq, wGram, Brow, ← sq_mul_sq Hd p σ hh hσ, ← rdiag_mul_rdiag]
  simp only [Matrix.conjTranspose_mul, rdiag_conjTranspose, Matrix.mul_assoc]
end Auto.HeatData
