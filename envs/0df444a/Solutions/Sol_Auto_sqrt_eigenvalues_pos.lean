-- Prove2me | solution 1 for Auto.sqrt_eigenvalues_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:26:08.697252+00:00
-- url     : https://prove2.me/submissions/bcfcf5eb-4ce0-437c-ab97-31b2d26192c1

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
theorem _root_.solution {P : Matrix n n ℂ} (hP : P.PosDef) (i : n) : 0 < √(hP.1.eigenvalues i) :=
  Real.sqrt_pos.2 (hP.eigenvalues_pos i)
end Auto
