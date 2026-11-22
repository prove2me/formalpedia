-- Prove2me | solution 1 for Auto.re_diag_le_of_sub_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:07:09.967385+00:00
-- url     : https://prove2.me/submissions/720eba0a-6ddf-4fa0-975c-404b86050e16

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
variable {n : Type*} [Fintype n] [DecidableEq n]
omit [Fintype n] [DecidableEq n]
namespace Auto
theorem _root_.solution {A B : Matrix n n ℂ} (hAB : (B - A).PosSemidef) (i : n) :
    (A i i).re ≤ (B i i).re := by
  have := hAB.diag_nonneg (i := i)
  rw [Matrix.sub_apply] at this
  have := (Complex.nonneg_iff.1 this).1
  rw [Complex.sub_re] at this
  linarith
end Auto
