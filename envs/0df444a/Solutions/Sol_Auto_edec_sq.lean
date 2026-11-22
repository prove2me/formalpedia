-- Prove2me | solution 1 for Auto.edec_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:48:12.465864+00:00
-- url     : https://prove2.me/submissions/56fa3902-7b6d-4798-86be-1e5283529cef

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
namespace Auto
theorem _root_.solution {b : ℝ} (x : ℝ) :
    edec b x ^ 2 = Real.exp (-(x ^ 2) / (8 * b)) := by
  rw [edec, sq, ← Real.exp_add]; congr 1; ring
end Auto
