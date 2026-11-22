-- Prove2me | solution 1 for Auto.dexp_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:53:54.569798+00:00
-- url     : https://prove2.me/submissions/c0fe4a5d-adda-4cc8-806b-38599f5124ac

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
open Auto
noncomputable section
namespace Auto
theorem _root_.solution (m : ℕ) (v : Fin 3) :
    dexp m v = 1 ∨ dexp m v = 2 := by
  unfold dexp; split_ifs <;> simp
end Auto
