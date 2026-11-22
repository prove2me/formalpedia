-- Prove2me | solution 1 for Auto.hsSq_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:29:19.119801+00:00
-- url     : https://prove2.me/submissions/0558428f-80b9-4503-9163-e20ade96a090

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
theorem _root_.solution {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℂ) :
    hsSq Aᴴ = hsSq A := by
  unfold hsSq; rw [Finset.sum_comm]; simp [Matrix.conjTranspose_apply]
end Auto
