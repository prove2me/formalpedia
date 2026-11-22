-- Prove2me | solution 1 for Auto.three_halves_sub_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:24:59.355793+00:00
-- url     : https://prove2.me/submissions/3b77e5b2-7c8d-47ed-8ac2-945eaeece2f2

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
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
namespace Auto
theorem _root_.solution {x η : ℝ} (hx : 0 ≤ x) (hη : 0 ≤ η) :
    0 ≤ (x + η) ^ (3 / 2 : ℝ) - η ^ (3 / 2 : ℝ) := by
  rw [sub_nonneg]
  exact Real.rpow_le_rpow hη (by linarith) (by norm_num)
end Auto
