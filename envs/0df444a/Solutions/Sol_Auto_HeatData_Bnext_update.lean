-- Prove2me | solution 1 for Auto.HeatData.Bnext_update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:34:55.830704+00:00
-- url     : https://prove2.me/submissions/5ea3aeb2-fb30-4b1c-9ada-456186957cd6

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
    Hd.Bnext (Function.update p k q) σ v = Hd.Bnext p σ v := by
  simp [Bnext, sq_update_ne Hd p σ hk.symm]
end Auto.HeatData
