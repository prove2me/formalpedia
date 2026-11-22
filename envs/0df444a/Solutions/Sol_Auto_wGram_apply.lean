-- Prove2me | solution 1 for Auto.wGram_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:31:31.141351+00:00
-- url     : https://prove2.me/submissions/3e2d9168-5728-4e61-9628-f39067052340

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
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
omit [DecidableEq κ] [Fintype κ]
namespace Auto
theorem _root_.solution (B : Matrix ι κ ℂ) (f : ι → ℝ) (a b : κ) :
    wGram B f a b = ∑ i, star (B i a) * (f i : ℂ) * B i b := by
  rw [wGram, Matrix.mul_apply]
  simp only [rdiag, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
end Auto
