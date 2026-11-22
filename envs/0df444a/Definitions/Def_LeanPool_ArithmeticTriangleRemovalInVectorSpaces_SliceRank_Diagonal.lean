-- Prove2me | Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_SliceRank_Diagonal
-- name    : LeanPool_ArithmeticTriangleRemovalInVectorSpaces_SliceRank_Diagonal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:08:44.837933+00:00
-- url     : https://prove2.me/theorems/1a72f2ff-ce73-4a5b-8bf3-bc4a6c1c52a0
-- title:
--   Diagonal
-- statement:
--   Definitions and structural lemmas for Diagonal, from Gabriel Dahia; LeanPool contributors; Terence Tao (pinned Mathlib Log.Sum support)'s pinned A tight bound for Green's arithmetic triangle removal lemma in vector spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/SliceRank/Diagonal.lean

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.LinearAlgebra.Matrix.Rank
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Finset Matrix Module
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {ι F : Type*} [Fintype ι] [Field F]
end ArithmeticTriangleRemovalInVectorSpaces


