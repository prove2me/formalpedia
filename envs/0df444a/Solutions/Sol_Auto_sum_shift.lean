-- Prove2me | solution 1 for Auto.sum_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:38:02.970021+00:00
-- url     : https://prove2.me/submissions/ddfa3bf4-6b61-4971-ba9c-efeaf4fca7a6

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
theorem _root_.solution (v : Fin 3) (q : Fin 2 → ℝ) (d : ℝ) :
    Function.update (planePt q) v (planePt q v + d) 0 +
      Function.update (planePt q) v (planePt q v + d) 1 +
      Function.update (planePt q) v (planePt q v + d) 2 = d := by
  fin_cases v <;> simp [planePt] <;> ring
end Auto
