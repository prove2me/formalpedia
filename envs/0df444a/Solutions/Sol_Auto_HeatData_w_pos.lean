-- Prove2me | solution 1 for Auto.HeatData.w_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:46:08.294577+00:00
-- url     : https://prove2.me/submissions/051354b3-c5f7-4393-a6a4-5a50462c4ef4

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
theorem _root_.solution (hh : 0 < Hd.h) {v : Fin 3} (hσ : 0 < σ v) (i : ι) : 0 < Hd.w p σ v i := by
  simp only [w, gweight, gaussian]
  have : 0 < √(2 * π * σ v) := Real.sqrt_pos.2 (by positivity)
  positivity
end Auto.HeatData
