-- Prove2me | solution 1 for Auto.HeatData.S_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:17:15.478798+00:00
-- url     : https://prove2.me/submissions/bfe99bba-0bef-47d4-8deb-b2bfb42481c5

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
theorem _root_.solution (v : Fin 3) :
    Hd.S p σ v = Hd.W p σ v * (Hd.W p σ v)ᴴ + (Hd.W p σ (v - 1))ᴴ * Hd.W p σ (v - 1) := by
  rw [S, R, rowMat, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromCols_mul_fromRows, Matrix.conjTranspose_conjTranspose]
end Auto.HeatData
