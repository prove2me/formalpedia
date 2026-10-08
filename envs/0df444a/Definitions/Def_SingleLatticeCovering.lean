-- Prove2me | Definitions.Def_SingleLatticeCovering
-- name    : SingleLatticeCovering
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:22.568982+00:00
-- url     : https://prove2.me/theorems/7be60440-1c0b-4b2d-8e03-5f299aca1d48
-- statement:
--   Space(n) is n-dimensional real coordinate space, the functions from Fin n to the reals. A set K in this space is a convex body, IsConvexBody(K), when it is compact, convex over the reals, and has nonempty interior. For a set K and a subgroup L of the space viewed as a module over the integers (any ℤ-submodule, with no further requirement such as discreteness or full rank), LatticeCovers(K,L) is the proposition that the Minkowski sum K + L, the set of all sums of a point of K and an element of L, equals the whole space. Equivalently, every point of the space lies in some translate of K by an element of L. These are definitions only; no theorem about such coverings is stated.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SingleLatticeCovering.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SingleLatticeCovering.lean; bytes 16..476
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-! Convex bodies and exact coverings by a single lattice in real coordinate space. -/

namespace SingleLatticeCovering

open MeasureTheory
open scoped Pointwise

abbrev Space (n : ℕ) := Fin n → ℝ

def IsConvexBody {n : ℕ} (K : Set (Space n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

def LatticeCovers {n : ℕ} (K : Set (Space n)) (L : Submodule ℤ (Space n)) : Prop :=
  K + (L : Set (Space n)) = Set.univ



end SingleLatticeCovering
end OAI


