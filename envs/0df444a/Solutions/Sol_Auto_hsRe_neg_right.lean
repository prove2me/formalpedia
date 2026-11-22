-- Prove2me | solution 1 for Auto.hsRe_neg_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:03:46.021599+00:00
-- url     : https://prove2.me/submissions/13159b9f-9587-4ea3-aecb-d5dff5ca7c65

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
variable {m n : Type*} [Fintype m] [Fintype n]
namespace Auto
theorem _root_.solution (X Y : Matrix m n ℂ) :
    hsRe X (-Y) = - hsRe X Y := by
  simp [hsRe, Matrix.mul_neg, Matrix.trace_neg]
end Auto
