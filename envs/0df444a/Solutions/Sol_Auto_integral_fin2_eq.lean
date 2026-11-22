-- Prove2me | solution 1 for Auto.integral_fin2_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:40:42.712602+00:00
-- url     : https://prove2.me/submissions/93f19518-1448-46d4-a8e5-4cd78a056df1

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
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ × ℝ → E) :
    ∫ x : Fin 2 → ℝ, f (x 0, x 1) = ∫ p, f p :=
  (volume_preserving_finTwoArrow ℝ).integral_comp' (g := f)
end Auto
