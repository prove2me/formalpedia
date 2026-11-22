-- Prove2me | solution 1 for Auto.two_div_sqrt_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:28:35.904564+00:00
-- url     : https://prove2.me/submissions/dc70d274-1bbe-4597-a965-b0cd819565f9

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
theorem _root_.solution : 2 * (√(2 * π))⁻¹ ≤ √(2 / π) := by
  rw [Real.le_sqrt (by positivity) (by positivity), mul_pow, inv_pow,
    Real.sq_sqrt (by positivity)]
  field_simp
  ring_nf
  rfl
end Auto
