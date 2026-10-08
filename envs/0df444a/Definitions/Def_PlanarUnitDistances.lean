-- Prove2me | Definitions.Def_PlanarUnitDistances
-- name    : PlanarUnitDistances
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:04.877195+00:00
-- url     : https://prove2.me/theorems/8c22e039-c225-4219-805e-bdeb4b0b3344
-- statement:
--   The plane is modelled as two-dimensional real Euclidean space. A pair of points, treated as an unordered pair (a Sym2 element), is a unit pair when the Euclidean distance between its two points equals 1; this is well defined because distance is symmetric. For a finite set X of points in the plane, unitPairCount(X) is the number of unordered pairs of points of X (taken from the symmetric square of X, so it includes pairs formed by a point with itself) that are unit pairs; since a point is at distance 0 from itself, such pairs never count, so this is the number of unordered pairs of distinct points of X at distance exactly 1. For a natural number n, u(n) is defined as the supremum of the set of values m for which some n-element finite planar set X has unitPairCount(X) = m, that is, the maximum possible number of unit distances determined by n points in the plane. These are only definitions; no bounds on u(n) are asserted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PlanarUnitDistances.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PlanarUnitDistances.lean; bytes 16..458
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace PlanarUnitDistances

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def IsUnitPair : Sym2 Plane → Prop :=
  Sym2.lift ⟨fun x y => dist x y = 1, fun x y => by dsimp; rw [dist_comm]⟩

noncomputable def unitPairCount (X : Finset Plane) : ℕ := by
  classical
  exact (X.sym2.filter IsUnitPair).card

noncomputable def u (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ X : Finset Plane, X.card = n ∧ unitPairCount X = m}



end PlanarUnitDistances
end OAI


