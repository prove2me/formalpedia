-- Prove2me | solution 1 for Auto.fromBlocks_diag_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:15:55.694113+00:00
-- url     : https://prove2.me/submissions/b5c1493b-38db-4192-bdad-ff7d16854ff9

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Auto
theorem _root_.solution (X Y : Matrix ι ι ℂ) :
    Matrix.fromBlocks X 0 0 Y = (ein1 : Matrix (ι ⊕ ι) ι ℂ) * X * (ein1 : Matrix (ι ⊕ ι) ι ℂ)ᴴ +
      (ein2 : Matrix (ι ⊕ ι) ι ℂ) * Y * (ein2 : Matrix (ι ⊕ ι) ι ℂ)ᴴ := by
  ext (a | a) (b | b) <;>
    simp [ein1, ein2, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
end Auto
