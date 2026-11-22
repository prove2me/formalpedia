-- Prove2me | solution 1 for Auto.HeatData.Mrow_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:18:35.017166+00:00
-- url     : https://prove2.me/submissions/2c05ba8b-b994-49cd-8d30-0402eb0b893f

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_rdiag_conjTranspose
public import Theorems.Thm_Auto_HeatData_Dc_eq

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
    Hd.Mrow p σ v = rdiag (Hd.dv p σ v) * wGram (rowMat (Hd.A v) (Hd.A (v - 1))) (fun i =>
      Hd.ddw p σ v i / 2) * rdiag (Hd.dv p σ v) := by
  rw [Mrow, wGram, wGram, Brow, Dc_eq]
  simp only [Matrix.conjTranspose_mul, rdiag_conjTranspose, Matrix.mul_assoc]
end Auto.HeatData
