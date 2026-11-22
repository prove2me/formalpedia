-- Prove2me | solution 1 for Auto.HeatData.sq_update_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:33:09.264262+00:00
-- url     : https://prove2.me/submissions/a6c9b58f-e2c0-4bf4-8bbc-1669699b2c8a

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_w_update_ne

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
omit [Fintype ι] [DecidableEq ι]
namespace Auto.HeatData
theorem _root_.solution {v k : Fin 3} (hk : k ≠ v) (q : ℝ) :
    Hd.sqw (Function.update p v q) σ k = Hd.sqw p σ k := by
  unfold HeatData.sqw; rw [w_update_ne Hd p σ hk]
end Auto.HeatData
