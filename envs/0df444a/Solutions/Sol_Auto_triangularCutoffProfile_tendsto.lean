-- Prove2me | solution 1 for Auto.triangularCutoffProfile_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:42:32.173308+00:00
-- url     : https://prove2.me/submissions/831b6e01-bedf-4fd0-aff9-fe57f068b9bb

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
theorem _root_.solution : Tendsto triangularCutoffProfile atTop (𝓝 0) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.sub
    ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul 2)
  convert h using 1
  · ext u; simp [triangularCutoffProfile]; ring
  · simp
end Auto
