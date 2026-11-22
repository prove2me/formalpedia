-- Prove2me | solution 1 for Auto.eigCoord_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:06:02.158173+00:00
-- url     : https://prove2.me/submissions/b2979ba3-ef3b-426d-a59f-e54b933ddbb8

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
open Auto
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
omit [Fintype m] [DecidableEq m]
namespace Auto
theorem _root_.solution {P : Matrix n n ℂ} (hP : P.IsHermitian) (K L : Matrix n n ℂ) :
    eigCoord hP (K + L) = eigCoord hP K + eigCoord hP L := by
  simp [eigCoord, Matrix.mul_add, Matrix.add_mul]
end Auto
