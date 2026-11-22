-- Prove2me | solution 1 for Auto.HeatData.tr32_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:46:45.259852+00:00
-- url     : https://prove2.me/submissions/775ddf2e-ad25-49d4-9b6a-929e150142df

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
theorem _root_.solution (η : ℝ) {κ : Type*} [Fintype κ] [DecidableEq κ] (Γ K : Matrix κ κ ℂ) (c : ℝ) :
    tr32 η Γ ((c : ℂ) • K) = c * tr32 η Γ K := by
  simp only [tr32, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]; ring
end Auto.HeatData
