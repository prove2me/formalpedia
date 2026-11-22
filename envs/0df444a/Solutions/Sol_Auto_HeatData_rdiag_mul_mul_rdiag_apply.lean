-- Prove2me | solution 1 for Auto.HeatData.rdiag_mul_mul_rdiag_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:46:51.406394+00:00
-- url     : https://prove2.me/submissions/2b555d4b-c145-474c-831f-a2f0cd9160ec

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
theorem _root_.solution {κ : Type*} [Fintype κ] [DecidableEq κ] (d d' : κ → ℝ)
    (M : Matrix κ κ ℂ) (a b : κ) :
    (rdiag d * M * rdiag d') a b = (d a : ℂ) * M a b * (d' b : ℂ) := by
  simp [rdiag, Matrix.mul_diagonal, Matrix.diagonal_mul]
end Auto.HeatData
