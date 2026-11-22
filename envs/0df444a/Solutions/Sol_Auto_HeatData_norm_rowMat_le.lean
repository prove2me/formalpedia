-- Prove2me | solution 1 for Auto.HeatData.norm_rowMat_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:23:54.864932+00:00
-- url     : https://prove2.me/submissions/cb1f68ed-064a-4aa6-9bc6-f8d5b5d3e465

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_norm_A_le

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
omit [DecidableEq ι]
namespace Auto.HeatData
theorem _root_.solution (v : Fin 3) (i : ι) (a : ι ⊕ ι) :
    ‖rowMat (Hd.A v) (Hd.A (v - 1)) i a‖ ≤ Hd.MA := by
  rcases a with j | j
  · simpa [rowMat] using Hd.norm_A_le v i j
  · simpa [rowMat, Matrix.conjTranspose_apply] using Hd.norm_A_le (v - 1) j i
end Auto.HeatData
