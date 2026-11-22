-- Prove2me | solution 1 for Auto.triangularCutoffProfile_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:42:21.444358+00:00
-- url     : https://prove2.me/submissions/f28c8698-c647-479b-82b3-63f9e359caed

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
theorem _root_.solution {u : ℝ} (hu : 0 ≤ u) : |triangularCutoffProfile u| ≤ 3 := by
  have he : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hp := Real.exp_pos (-u)
  have hm : u * Real.exp (-u) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one u).trans (Real.exp_le_one_iff.mpr (by norm_num))
  rw [triangularCutoffProfile, abs_le]
  constructor <;> nlinarith
end Auto
