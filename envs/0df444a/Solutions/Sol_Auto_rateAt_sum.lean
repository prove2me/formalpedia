-- Prove2me | solution 1 for Auto.rateAt_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:36:18.07996+00:00
-- url     : https://prove2.me/submissions/a340a7b6-bc42-43e8-8fe2-6c1ea09853a3

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
theorem _root_.solution (v : Fin 3) :
    rateAt v 0 + rateAt v 1 + rateAt v 2 = 16 / 5 := by
  fin_cases v <;> simp [rateAt] <;> norm_num
end Auto
