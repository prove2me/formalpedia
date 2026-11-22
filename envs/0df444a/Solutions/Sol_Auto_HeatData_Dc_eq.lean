-- Prove2me | solution 1 for Auto.HeatData.Dc_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:33:54.448188+00:00
-- url     : https://prove2.me/submissions/fffdaefd-fb06-4bb1-a5a6-4043119d3ce0

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
omit [Fintype ι]
namespace Auto.HeatData
theorem _root_.solution (v : Fin 3) : Hd.Dc p σ v = rdiag (Hd.dv p σ v) := by
  rw [Dc, rdiag, rdiag, rdiag, Matrix.fromBlocks_diagonal]
  congr 1; funext a; rcases a with a | a <;> rfl
end Auto.HeatData
