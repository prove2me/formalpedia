-- Prove2me | solution 1 for Auto.sig_rateAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:36:43.937431+00:00
-- url     : https://prove2.me/submissions/f75e0da0-ad23-4312-9420-fa82e7a11d35

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
theorem _root_.solution (v : Fin 3) (s : ℝ) :
    HeatData.sig (rateAt v) s = Function.update (fun _ => 11 / 10 * s) v s := by
  funext k
  simp only [HeatData.sig, rateAt, Function.update_apply]
  split_ifs <;> ring
end Auto
