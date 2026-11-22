-- Prove2me | solution 1 for Auto.rateAt_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:35:11.252156+00:00
-- url     : https://prove2.me/submissions/33546a07-5199-4fc1-97d1-b0d1768fceb0

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
theorem _root_.solution (v : Fin 3) : ∀ k, rateAt v k = 1 ∨ rateAt v k = 11 / 10 := fun k => by
  unfold rateAt; split_ifs <;> simp
end Auto
