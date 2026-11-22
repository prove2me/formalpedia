-- Prove2me | Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Monomials
-- name    : LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Monomials
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:08:39.169349+00:00
-- url     : https://prove2.me/theorems/a1ccc6ad-284f-4e26-94a6-28b55ab27133
-- title:
--   Monomials
-- statement:
--   Definitions and structural lemmas for Monomials, from Gabriel Dahia; LeanPool contributors; Terence Tao (pinned Mathlib Log.Sum support)'s pinned A tight bound for Green's arithmetic triangle removal lemma in vector spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Monomials.lean

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace ArithmeticTriangleRemovalInVectorSpaces
def lowDegreeExponents (p d : ℕ) : Finset (Fin d → ℕ) :=
  {α ∈ Fintype.piFinset fun _ ↦ range p | 3 * ∑ t, α t ≤ (p - 1) * d}
end ArithmeticTriangleRemovalInVectorSpaces


