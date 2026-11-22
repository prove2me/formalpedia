-- Prove2me | solution 1 for Auto.hsSq_fromCols
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:29:10.761854+00:00
-- url     : https://prove2.me/submissions/646eda1d-32d0-4f7d-97c3-0cbbe40805be

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
theorem _root_.solution {ι κ : Type*} [Fintype ι] [Fintype κ] (A B : Matrix ι κ ℂ) :
    hsSq (Matrix.fromCols A B) = hsSq A + hsSq B := by
  simp [hsSq, Fintype.sum_sum_type, Finset.sum_add_distrib]
end Auto
