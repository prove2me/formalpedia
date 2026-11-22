-- Prove2me | solution 1 for Auto.HeatData.R_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:33:57.345882+00:00
-- url     : https://prove2.me/submissions/1358fd2c-bbbb-414d-b0f5-dc0bc4e98ebd

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_rdiag_conjTranspose

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
theorem _root_.solution (v : Fin 3) :
    Hd.R p σ v = rdiag (Hd.sqw p σ v) * rowMat (Hd.A v) (Hd.A (v - 1)) * Hd.Dc p σ v := by
  have hv : v - 1 + 1 = v := by abel
  simp only [R, W, rowMat, Dc, hv, Matrix.conjTranspose_mul, rdiag_conjTranspose]
  rw [Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks]
  simp [Matrix.mul_assoc]
end Auto.HeatData
