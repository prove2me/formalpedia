-- Prove2me | solution 1 for Auto.sum_eigenvalues_eq_roots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:03:48.937813+00:00
-- url     : https://prove2.me/submissions/ea21c616-ca7c-4b65-8934-8474617f4dc7

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
theorem _root_.solution (g : ℂ → ℝ) {P : Matrix n n ℂ} (hP : P.IsHermitian) :
    ∑ i, g (hP.eigenvalues i) = (P.charpoly.roots.map g).sum := by
  rw [hP.roots_charpoly_eq_eigenvalues, Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl
end Auto
