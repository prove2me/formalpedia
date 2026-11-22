-- Prove2me | solution 1 for Auto.HeatData.rdiag_mul_rdiag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:24:16.58904+00:00
-- url     : https://prove2.me/submissions/f536e1c8-98fb-4b31-9e8c-603885829ced

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
namespace Auto.HeatData
theorem _root_.solution (f g : ι → ℝ) :
    rdiag f * rdiag g = rdiag (f * g) := by
  simp [rdiag, Matrix.diagonal_mul_diagonal]
end Auto.HeatData
