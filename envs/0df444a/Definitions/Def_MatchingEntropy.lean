-- Prove2me | Definitions.Def_MatchingEntropy
-- name    : MatchingEntropy
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:18.288721+00:00
-- url     : https://prove2.me/theorems/380c91ce-68a2-40d3-8f20-894923f385d5
-- statement:
--   The block sets up a maximum-entropy problem over perfect matchings. probabilitySimplex(Index) is the set of nonnegative real weight vectors on a finite index type summing to 1. A LooplessGraph on finite vertex type V and edge type E is given by maps assigning each edge a left and a right endpoint, with the two endpoints always distinct; parallel edges are allowed. An edge is incident to a vertex if that vertex is its left or right endpoint. A set M of edges is a perfect matching if every vertex has exactly one incident edge in M. Matching(G) is the finite type of perfect matchings of G. The indicator of a matching M is the 0/1 vector on edges that equals 1 exactly on edges of M, and the polytope of G is the convex hull in ℝ^E of all these indicator vectors. For a weight function p on matchings, mean(p) is the edge vector with e-th coordinate the sum over M of p(M) times the indicator of M at e, the marginal probability of edge e. Given a target y in ℝ^E, feasibleLaws(G,y) is the set of probability vectors p on matchings, in the simplex, whose mean equals y. The entropy of a finite real vector p is the sum of negMulLog(p_i), that is the sum of −p_i log p_i, and marginalEntropy(y) is this entropy applied directly to the edge vector y. Finally maxMatchingEntropy(G,y) is the supremum of the entropies of the feasible laws; this is a real supremum, and it is 0 under Lean's convention if the feasible set is empty (for example when y is outside the polytope).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MatchingEntropy.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MatchingEntropy.lean; bytes 16..1677
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace MatchingEntropy

/-- Nonnegative real weights with total mass one. -/
def probabilitySimplex (Index : Type*) [Fintype Index] : Set (Index → ℝ) :=
  {weights | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1}

structure LooplessGraph (V E : Type*) where
  left : E → V
  right : E → V
  loopless : ∀ e, left e ≠ right e

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

def Incident (G : LooplessGraph V E) (v : V) (e : E) : Prop :=
  G.left e = v ∨ G.right e = v

def IsPerfectMatching (G : LooplessGraph V E) (M : Finset E) : Prop :=
  ∀ v, ∃! e, e ∈ M ∧ G.Incident v e

abbrev Matching (G : LooplessGraph V E) := {M : Finset E // G.IsPerfectMatching M}

instance matchingFintype (G : LooplessGraph V E) : Fintype G.Matching :=
  Fintype.ofFinite _

def indicator (G : LooplessGraph V E) (M : G.Matching) (e : E) : ℝ :=
  if e ∈ M.val then 1 else 0

def polytope (G : LooplessGraph V E) : Set (E → ℝ) :=
  convexHull ℝ (Set.range G.indicator)

def mean (G : LooplessGraph V E) (p : G.Matching → ℝ) (e : E) : ℝ :=
  ∑ M, p M * G.indicator M e

def feasibleLaws (G : LooplessGraph V E) (y : E → ℝ) : Set (G.Matching → ℝ) :=
  {p | p ∈ probabilitySimplex G.Matching ∧ G.mean p = y}

end LooplessGraph

def entropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

def marginalEntropy (y : E → ℝ) : ℝ := entropy y

def maxMatchingEntropy (G : LooplessGraph V E) (y : E → ℝ) : ℝ :=
  sSup (entropy '' G.feasibleLaws y)



end MatchingEntropy
end
end OAI


