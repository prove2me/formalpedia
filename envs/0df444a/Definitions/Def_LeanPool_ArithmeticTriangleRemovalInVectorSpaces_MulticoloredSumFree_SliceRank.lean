-- Prove2me | Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_SliceRank
-- name    : LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_SliceRank
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:09:04.765466+00:00
-- url     : https://prove2.me/theorems/68520c2d-bd43-42f9-b4ae-e33bbfbd3a3e
-- title:
--   Slice Rank
-- statement:
--   Definitions and structural lemmas for Slice Rank, from Gabriel Dahia; LeanPool contributors; Terence Tao (pinned Mathlib Log.Sum support)'s pinned A tight bound for Green's arithmetic triangle removal lemma in vector spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/SliceRank.lean

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Monomials
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_SliceRank_Diagonal
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.FieldTheory.Finite.Basic
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Finset MvPolynomial
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {p : ℕ} [Fact p.Prime]
end ArithmeticTriangleRemovalInVectorSpaces


