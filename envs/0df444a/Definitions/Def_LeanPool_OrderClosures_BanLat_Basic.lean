-- Prove2me | Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
-- name    : LeanPool_OrderClosures_BanLat_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:10:18.096201+00:00
-- url     : https://prove2.me/theorems/c3ac73ed-35d9-4568-b4e2-a511a8d3f095
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean

module
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
set_option autoImplicit true
@[expose] public section
@[expose] public section
class VectorLattice (X : Type*) [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] extends
  Module ℝ X,
  PosSMulMono ℝ X
noncomputable instance : VectorLattice ℝ where
section LatticeOrderedGroup
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
variable (x : X)
end LatticeOrderedGroup
section VectorLattice
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
variable (x y : X)
section Archimedean
class IsVLArchimedean (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] : Prop where
  le_zero_of_forall_nsmul_le {x y : X} :
    (∀ n : ℕ, n • x ≤ y) → x ≤ 0
namespace IsVLArchimedean
end IsVLArchimedean
variable [IsVLArchimedean X]
end Archimedean
end VectorLattice


