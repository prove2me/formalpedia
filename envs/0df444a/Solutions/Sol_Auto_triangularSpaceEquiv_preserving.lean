-- Prove2me | solution 1 for Auto.triangularSpaceEquiv_preserving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:28:59.289261+00:00
-- url     : https://prove2.me/submissions/fcec25b7-7e24-46df-b609-35373ac9e304

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
theorem _root_.solution : MeasurePreserving triangularSpaceEquiv := by
  apply (MeasurePreserving.id (volume : Measure (ℝ × ℝ))).skew_product
    (g := fun p t => -p.1 - p.2 - t) (μc := volume) (μd := volume) (by fun_prop)
  filter_upwards [] with p
  convert ((measurePreserving_add_left volume (-p.1 - p.2)).comp
    (Measure.measurePreserving_neg volume)).map_eq using 1
  simp only [Function.comp_def, sub_eq_add_neg]
end Auto
