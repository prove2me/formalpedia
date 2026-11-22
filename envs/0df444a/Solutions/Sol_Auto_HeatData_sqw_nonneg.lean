-- Prove2me | solution 1 for Auto.HeatData.sqw_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:24:21.709798+00:00
-- url     : https://prove2.me/submissions/9394ab54-951e-4596-ba97-c1d25dce9133

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
variable (Hd : HeatData ι)
omit [Fintype ι] [DecidableEq ι]
namespace Auto.HeatData
theorem _root_.solution (p σ : Fin 3 → ℝ) (k : Fin 3) (i : ι) : 0 ≤ Hd.sqw p σ k i := Real.sqrt_nonneg _
end Auto.HeatData
