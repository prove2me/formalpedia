-- Prove2me | solution 1 for Auto.eigCoord_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:06:17.499741+00:00
-- url     : https://prove2.me/submissions/60aba1d3-a576-408e-a6a3-60db491d8c06

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
    eigCoord hP (K - L) = eigCoord hP K - eigCoord hP L := by
  simp [eigCoord, Matrix.mul_sub, Matrix.sub_mul]
end Auto
