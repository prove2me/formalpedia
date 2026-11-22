-- Prove2me | solution 1 for Auto.gaussian_anti
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:28:31.069633+00:00
-- url     : https://prove2.me/submissions/517f33a5-4ecf-4137-b869-fe251bae566a

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
theorem _root_.solution {σ : ℝ} (hσ : 0 < σ) {t t' : ℝ} (h : |t| ≤ |t'|) :
    gaussian σ t' ≤ gaussian σ t := by
  unfold gaussian
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  rw [neg_div, neg_div, neg_le_neg_iff]
  exact div_le_div_of_nonneg_right (sq_le_sq.2 h) (by positivity)
end Auto
