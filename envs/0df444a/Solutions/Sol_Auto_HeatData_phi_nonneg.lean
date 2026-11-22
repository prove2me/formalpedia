-- Prove2me | solution 1 for Auto.HeatData.phi_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:48:33.298803+00:00
-- url     : https://prove2.me/submissions/7113185a-bf94-4f95-b87e-bafcea2239a0

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_edec_pos

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
theorem _root_.solution (b : ℝ) (v : Fin 3) (p : Fin 3 → ℝ) : 0 ≤ phi b v p := by
  unfold phi; have := edec_pos b (p v); have := edec_pos b (p (v + 1))
  have := edec_pos b (p (v - 1)); positivity
end Auto.HeatData
