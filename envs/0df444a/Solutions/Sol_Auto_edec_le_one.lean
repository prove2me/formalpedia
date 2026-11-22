-- Prove2me | solution 1 for Auto.edec_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:21:47.844348+00:00
-- url     : https://prove2.me/submissions/82c0e9fc-c3f7-4213-ad82-b6282d35b9cf

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
theorem _root_.solution {b : ℝ} (hb : 0 < b) (x : ℝ) : edec b x ≤ 1 := by
  rw [edec, Real.exp_le_one_iff]
  have := sq_nonneg x
  rw [neg_div, neg_nonpos]; positivity
end Auto
