-- Prove2me | solution 1 for Auto.HeatData.Brow_update2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:34:32.136598+00:00
-- url     : https://prove2.me/submissions/3808a099-420a-4d72-849b-623389a01cb3

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_Brow_update
public import Theorems.Thm_P2M_Auto_HeatData_Brow_update___289bec5b5b62

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
theorem _root_.solution (p σ : Fin 3 → ℝ) (v : Fin 3) (q τ : ℝ) :
    Hd.Brow (Function.update p v q) (Function.update σ v τ) v = Hd.Brow p σ v := by
  rw [Brow_update, Brow_update_σ]
end Auto.HeatData
