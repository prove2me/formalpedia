-- Prove2me | solution 1 for Auto.trF_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:31:29.685284+00:00
-- url     : https://prove2.me/submissions/09b8107c-d82f-427a-bc49-45ea15f46036

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_trace_conj_unitary

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
theorem _root_.solution (f : ℝ → ℝ) {P : Matrix n n ℂ} (hP : P.IsHermitian) :
    trF f P = ∑ i, f (hP.eigenvalues i) := by
  rw [trF, hP.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, trace_conj_unitary]
  simp [Matrix.trace_diagonal]
end Auto
