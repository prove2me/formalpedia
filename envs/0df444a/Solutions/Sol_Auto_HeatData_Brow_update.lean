-- Prove2me | solution 1 for Auto.HeatData.Brow_update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:34:53.131254+00:00
-- url     : https://prove2.me/submissions/a2763abb-3086-46c6-be95-b2a564ae5144

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_fin3_ne_succ
public import Theorems.Thm_Auto_HeatData_fin3_ne_pred
public import Theorems.Thm_Auto_HeatData_sq_update_ne

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
theorem _root_.solution (v : Fin 3) (q : ℝ) : Hd.Brow (Function.update p v q) σ v = Hd.Brow p σ v := by
  simp [Brow, Dc, sq_update_ne Hd p σ (fin3_ne_succ v).symm,
    sq_update_ne Hd p σ (fin3_ne_pred v).symm]
end Auto.HeatData
