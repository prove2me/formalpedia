-- Prove2me | solution 1 for Auto.HeatData.w_update_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:32:02.257889+00:00
-- url     : https://prove2.me/submissions/da6f14c6-04db-4754-8c2d-7db3be1c06d2

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT

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
    Hd.w (Function.update p v q) σ k = Hd.w p σ k := by
  simp [w, Function.update_of_ne hk]
end Auto.HeatData
