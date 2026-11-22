-- Prove2me | solution 1 for Auto.HeatData.ddw_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:27:20.350918+00:00
-- url     : https://prove2.me/submissions/29b475df-4477-4c61-8617-86dc7be3c9ce

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
theorem _root_.solution (v : Fin 3) : Hd.ddw p σ v = fun i => Hd.h * gaussianD 2 (σ v) (Hd.u i - p v) := rfl
end Auto.HeatData
