-- Prove2me | solution 1 for Auto.gaussian_le_sup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:51:04.230476+00:00
-- url     : https://prove2.me/submissions/34e65b2c-b8bf-48fc-bc7c-6f28deec34bf

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
theorem _root_.solution (σ t : ℝ) : gaussian σ t ≤ (√(2 * π * σ))⁻¹ := by
  unfold gaussian
  have : Real.exp (-(t ^ 2) / (2 * σ)) ≤ 1 ∨ σ ≤ 0 := by
    rcases le_or_gt σ 0 with h | h
    · exact Or.inr h
    · left; rw [Real.exp_le_one_iff]; have := sq_nonneg t; rw [neg_div, neg_nonpos]; positivity
  rcases this with h | h
  · exact mul_le_of_le_one_right (by positivity) h
  · have : √(2 * π * σ) = 0 := Real.sqrt_eq_zero'.2 (by nlinarith [Real.pi_pos])
    simp [this]
end Auto
