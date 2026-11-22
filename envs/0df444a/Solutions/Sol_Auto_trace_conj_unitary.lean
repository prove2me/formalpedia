-- Prove2me | solution 1 for Auto.trace_conj_unitary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:29:49.181028+00:00
-- url     : https://prove2.me/submissions/500aa0e5-2138-4bba-82b1-4bb56346041e

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
omit [DecidableEq m]
namespace Auto
theorem _root_.solution (U : Matrix.unitaryGroup n ℂ) (D : Matrix n n ℂ) :
    ((U : Matrix n n ℂ) * D * star (U : Matrix n n ℂ)).trace = D.trace := by
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]
end Auto
