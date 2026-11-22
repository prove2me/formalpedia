-- Prove2me | solution 1 for Auto.exp_shift_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:20:34.749218+00:00
-- url     : https://prove2.me/submissions/489345a3-0286-4758-802b-de4c5d6ae359

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
theorem _root_.solution (u q : ℝ) {c : ℝ} (hc : 0 < c) :
    Real.exp (-((u - q) ^ 2) / (4 * c)) ≤ Real.exp (u ^ 2 / (4 * c)) * Real.exp (-(q ^ 2) / (8 *
      c)) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have : -((u - q) ^ 2) ≤ u ^ 2 - q ^ 2 / 2 := by nlinarith [sq_nonneg (2 * u - q)]
  rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by
      positivity)]
  nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 32 * c ^ 2)]
end Auto
