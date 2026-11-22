-- Prove2me | solution 1 for Auto.dexp_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:52:50.242688+00:00
-- url     : https://prove2.me/submissions/8d3ff307-080e-4dd9-bbbe-1bfbdd8ca68a

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
theorem _root_.solution {m : ℕ} (hm : m = 3 ∨ m = 4) :
    dexp m 2 + dexp m 1 + dexp m 0 = m := by
  rcases hm with rfl | rfl <;> simp [dexp]
end Auto
