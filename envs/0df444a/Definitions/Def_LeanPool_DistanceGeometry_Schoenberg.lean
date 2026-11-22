-- Prove2me | Definitions.Def_LeanPool_DistanceGeometry_Schoenberg
-- name    : LeanPool_DistanceGeometry_Schoenberg
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:45:20.055845+00:00
-- url     : https://prove2.me/theorems/d74b3eb5-c940-43e0-943d-7f733e35deec
-- title:
--   Schoenberg
-- statement:
--   Definitions and structural lemmas for Schoenberg, from Egor Lyfar; LeanPool contributors's pinned Euclidean distance geometry development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Schoenberg.lean

module
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Algebra.Order.Star.Real
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DistanceGeometry
open Matrix
open scoped RealInnerProductSpace
variable {n k : ℕ} [NeZero n]
end DistanceGeometry


