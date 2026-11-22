-- Prove2me | Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_LinearMap_Card
-- name    : LeanPool_ArithmeticTriangleRemovalInVectorSpaces_LinearMap_Card
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:08:38.604795+00:00
-- url     : https://prove2.me/theorems/fd22a840-70e4-4aed-aed5-a3ed720768b1
-- title:
--   Card
-- statement:
--   Definitions and structural lemmas for Card, from Gabriel Dahia; LeanPool contributors; Terence Tao (pinned Mathlib Log.Sum support)'s pinned A tight bound for Green's arithmetic triangle removal lemma in vector spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/LinearMap/Card.lean

module
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Basis.VectorSpace
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Module
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {r : ℕ} {v : Fin r → V}
instance LinearMap.finite_of_finite [Finite V] [Finite W] : Finite (V →ₗ[K] W) :=
  Finite.of_injective _ DFunLike.coe_injective


