-- Prove2me | solution 1 for Auto.nNorm_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:39:23.154684+00:00
-- url     : https://prove2.me/submissions/3617b86b-c9fc-4d29-ba10-f58c2546286b

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
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
public section
open Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace Auto
theorem _root_.solution {ι : Type*} [Fintype ι] (h : ℝ) (A : Matrix ι ι ℂ) :
    nNorm h A ^ 3 = h ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 3 := by
  rw [nNorm, ← Real.rpow_natCast,
    ← Real.rpow_mul (mul_nonneg (sq_nonneg h) (by positivity))]
  norm_num
end Auto
