-- Prove2me | solution 1 for Auto.gdom_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:26:42.084716+00:00
-- url     : https://prove2.me/submissions/8d8aa7de-2af9-44fa-a582-c0b5dc0467b8

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
theorem _root_.solution (ε : ℝ) (p : Fin 3 → ℝ) :
    gdom ε p = Real.exp (-ε * (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2)) := by
  rw [gdom, Fin.prod_univ_three, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
end Auto
