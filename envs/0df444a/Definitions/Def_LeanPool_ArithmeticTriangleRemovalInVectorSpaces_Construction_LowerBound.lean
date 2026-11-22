-- Prove2me | Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_LowerBound
-- name    : LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_LowerBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:12:07.825646+00:00
-- url     : https://prove2.me/theorems/f48f8889-9aa8-4c8b-90ac-189e2c76a91e
-- title:
--   Lower Bound
-- statement:
--   Definitions and structural lemmas for Lower Bound, from Gabriel Dahia; LeanPool contributors; Terence Tao (pinned Mathlib Log.Sum support)'s pinned A tight bound for Green's arithmetic triangle removal lemma in vector spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/LowerBound.lean

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_Family
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Decreasing
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Ring.GeomSum
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Finset Real
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {n N : ℕ} {ρ : ℝ}
noncomputable def geomDist (N : ℕ) (ρ : ℝ) (k : ℕ) : ℝ :=
  ρ ^ k / ∑ j ∈ range (N + 1), ρ ^ j
end ArithmeticTriangleRemovalInVectorSpaces


