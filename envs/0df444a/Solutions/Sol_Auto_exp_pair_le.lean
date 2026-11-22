-- Prove2me | solution 1 for Auto.exp_pair_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:26:52.796494+00:00
-- url     : https://prove2.me/submissions/ce3b135b-0351-4c7d-b2e0-a524515ffe0d

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
theorem _root_.solution (a b c : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.exp (-(a ^ 2 + b ^ 2) * x) * Real.exp (-(a + b + c) ^ 2 * y) ≤ Real.exp (-(min x y / 4)
      * (a ^ 2 + b ^ 2 + c ^ 2)) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  set m := min x y
  have hm : 0 < m := lt_min hx hy
  have hmx : m ≤ x := min_le_left _ _
  have hmy : m ≤ y := min_le_right _ _
  set S := a + b + c
  have hc : c ^ 2 ≤ 3 * (S ^ 2 + a ^ 2 + b ^ 2) := by
    have : c = S - a - b := by simp only [S]; ring
    rw [this]; nlinarith [sq_nonneg (S + a), sq_nonneg (S + b), sq_nonneg (a - b)]
  have h1 : m * (a ^ 2 + b ^ 2) ≤ x * (a ^ 2 + b ^ 2) :=
    mul_le_mul_of_nonneg_right hmx (by positivity)
  have h2 : m * S ^ 2 ≤ y * S ^ 2 := mul_le_mul_of_nonneg_right hmy (by positivity)
  nlinarith
end Auto
