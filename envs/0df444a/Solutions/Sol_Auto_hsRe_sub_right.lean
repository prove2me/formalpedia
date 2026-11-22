-- Prove2me | solution 1 for Auto.hsRe_sub_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:04:56.345731+00:00
-- url     : https://prove2.me/submissions/0034bb3e-a04e-4daa-8d5e-df95f5113327

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_hsRe_neg_right

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Auto
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n]
namespace Auto
theorem _root_.solution (X Y Z : Matrix m n ℂ) :
    hsRe X (Y - Z) = hsRe X Y - hsRe X Z := by
  rw [sub_eq_add_neg, hsRe_add_right, hsRe_neg_right, ← sub_eq_add_neg]
end Auto
