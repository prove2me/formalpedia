-- Prove2me | solution 1 for Auto.HeatData.dw_update2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:34:49.338322+00:00
-- url     : https://prove2.me/submissions/d0489cfc-9b47-48bf-b144-9372b6214f18

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_dw_def

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
omit [Fintype ι] [DecidableEq ι]
namespace Auto.HeatData
theorem _root_.solution (p σ : Fin 3 → ℝ) (v : Fin 3) (q τ : ℝ) :
    Hd.dw (Function.update p v q) (Function.update σ v τ) v = fun i => -(Hd.h * gaussianD 1 τ
      (Hd.u i - q)) := by
  rw [dw_def]; simp
end Auto.HeatData
