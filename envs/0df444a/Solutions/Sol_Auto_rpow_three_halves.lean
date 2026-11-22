-- Prove2me | solution 1 for Auto.rpow_three_halves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:24:50.777812+00:00
-- url     : https://prove2.me/submissions/db751f5b-c3c0-4d18-8cb7-37f5df0e952b

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
theorem _root_.solution {y : ℝ} (hy : 0 ≤ y) : y ^ (3 / 2 : ℝ) = √y ^ 3 := by
  rw [show (3 / 2 : ℝ) = (1 / 2) * ((3 : ℕ) : ℝ) by norm_num, Real.rpow_mul_natCast hy,
    ← Real.sqrt_eq_rpow]
end Auto
