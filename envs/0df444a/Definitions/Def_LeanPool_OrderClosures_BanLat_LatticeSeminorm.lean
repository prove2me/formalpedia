-- Prove2me | Definitions.Def_LeanPool_OrderClosures_BanLat_LatticeSeminorm
-- name    : LeanPool_OrderClosures_BanLat_LatticeSeminorm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:10:41.829233+00:00
-- url     : https://prove2.me/theorems/0cc9cb72-9bd3-4df6-bea0-292bed485f91
-- title:
--   Lattice Seminorm
-- statement:
--   Definitions and structural lemmas for Lattice Seminorm, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LatticeSeminorm.lean

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped Topology Pointwise
universe u v
structure LatticeSeminorm (E : Type u) [AddCommGroup E] [Lattice E]
    [IsOrderedAddMonoid E] [VectorLattice E] extends Seminorm ℝ E where
  /-- Monotonicity with respect to the lattice absolute value. -/
  monotone_abs' : ∀ {x y : E}, |x| ≤ |y| → toSeminorm x ≤ toSeminorm y
namespace LatticeSeminorm
variable {E : Type u} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [VectorLattice E]
abbrev toSeminormFamily {ι : Type v} (p : ι → LatticeSeminorm E) : SeminormFamily ℝ E ι :=
  fun i => (p i).toSeminorm
end LatticeSeminorm


