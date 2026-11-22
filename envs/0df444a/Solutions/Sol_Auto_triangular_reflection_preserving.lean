-- Prove2me | solution 1 for Auto.triangular_reflection_preserving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:42:46.799384+00:00
-- url     : https://prove2.me/submissions/5212adf2-5b7c-48f7-8422-31864266cbad

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
theorem _root_.solution :
    MeasurePreserving (fun q : (ℝ × ℝ) × ℝ => (q.1, -q.2)) := by
  exact (MeasurePreserving.id (volume : Measure (ℝ × ℝ))).prod
    (Measure.measurePreserving_neg (volume : Measure ℝ))
end Auto
