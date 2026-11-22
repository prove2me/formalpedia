-- Prove2me | solution 1 for Auto.HeatData.Bprev_update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:34:42.267873+00:00
-- url     : https://prove2.me/submissions/ceb48544-2131-41c1-9b1d-07e439530e60

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
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
theorem _root_.solution {v k : Fin 3} (hk : k ≠ v) (q : ℝ) :
    Hd.Bprev (Function.update p k q) σ v = Hd.Bprev p σ v := by
  simp [Bprev, sq_update_ne Hd p σ hk.symm]
end Auto.HeatData
