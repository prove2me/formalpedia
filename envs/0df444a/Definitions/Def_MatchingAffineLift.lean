-- Prove2me | Definitions.Def_MatchingAffineLift
-- name    : MatchingAffineLift
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:18.221721+00:00
-- url     : https://prove2.me/theorems/0e903c46-a927-4d37-bf3c-0b09b42adae8
-- statement:
--   An edge on n vertices is a pair (i,j) of elements of Fin n with i<j. A set M of edges is a perfect matching when every vertex v lies in exactly one edge of M, that is, exactly one edge of M has v as an endpoint; PerfectMatching(n) is the type of such sets. For a perfect matching M, matchingPoint(M) is its 0/1 indicator vector in ℝ^Edge, with value 1 on edges in M and 0 elsewhere, and matchingPolytope(n) is the convex hull in ℝ^Edge of all these indicator vectors, the perfect matching polytope of the complete graph on n vertices. HasAffineLift(n,r) is a defined proposition, not an established theorem, saying that this polytope is a positive semidefinite lift of size r: there exist an affine subspace L of the space of real r×r matrices and an affine map T from r×r real matrices to ℝ^Edge such that the image under T of the set of positive semidefinite matrices lying in L is exactly the matching polytope. Here the positive semidefinite condition is Mathlib's PosSemidef for matrices, which includes Hermitian symmetry.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MatchingAffineLift.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MatchingAffineLift.lean; bytes 16..841
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace PerfectMatchingPSD

abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

def IsPerfectMatching {n : ℕ} (M : Finset (Edge n)) : Prop :=
  ∀ v : Fin n, (M.filter fun e => e.1.1 = v ∨ e.1.2 = v).card = 1

abbrev PerfectMatching (n : ℕ) :=
  {M : Finset (Edge n) // IsPerfectMatching M}

noncomputable def matchingPoint {n : ℕ} (M : PerfectMatching n) : Edge n → ℝ := by
  classical
  exact fun e => if e ∈ M.1 then 1 else 0

noncomputable def matchingPolytope (n : ℕ) : Set (Edge n → ℝ) :=
  convexHull ℝ (Set.range (matchingPoint (n := n)))

def HasAffineLift (n r : ℕ) : Prop :=
  ∃ (L : AffineSubspace ℝ (Matrix (Fin r) (Fin r) ℝ))
    (T : Matrix (Fin r) (Fin r) ℝ →ᵃ[ℝ] (Edge n → ℝ)),
    T '' {X | X ∈ L ∧ X.PosSemidef} = matchingPolytope n



end PerfectMatchingPSD
end OAI


