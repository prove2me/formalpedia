-- Prove2me | solution 1 for Auto.HeatData.tr32_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:17:35.335799+00:00
-- url     : https://prove2.me/submissions/b5bd3000-6e14-434f-be29-424149b83c04

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
namespace Auto.HeatData
theorem _root_.solution (η : ℝ) {κ : Type*} [Fintype κ] [DecidableEq κ] (Γ K L : Matrix κ κ ℂ) :
    tr32 η Γ (K + L) = tr32 η Γ K + tr32 η Γ L := by
  simp only [tr32, Matrix.mul_add, Matrix.trace_add, Complex.add_re]; ring
end Auto.HeatData
