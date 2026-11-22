-- Prove2me | solution 1 for Auto.fromBlocks_diag_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:17:37.394915+00:00
-- url     : https://prove2.me/submissions/8fb41584-a88b-426c-996e-c73e998c7c14

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_fromBlocks_diag_eq

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
omit [DecidableEq ι] [Fintype ι]
namespace Auto
theorem _root_.solution [Finite ι] {X Y : Matrix ι ι ℂ} (hX : X.PosSemidef)
    (hY : Y.PosSemidef) :
    (Matrix.fromBlocks X 0 0 Y).PosSemidef := by
  classical
  let := Fintype.ofFinite ι
  rw [fromBlocks_diag_eq]
  exact (hX.mul_mul_conjTranspose_same _).add (hY.mul_mul_conjTranspose_same _)
end Auto
