-- Prove2me | solution 1 for Auto.integrable_gdom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:50:11.360475+00:00
-- url     : https://prove2.me/submissions/155c16fd-8fec-41ea-aa5b-979fae8956b2

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
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) : Integrable (gdom ε) :=
  Integrable.fintype_prod (f := fun _ x => Real.exp (-ε * x ^ 2))
    fun _ => integrable_exp_neg_mul_sq hε
end Auto
