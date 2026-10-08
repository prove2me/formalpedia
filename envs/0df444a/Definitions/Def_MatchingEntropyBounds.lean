-- Prove2me | Definitions.Def_MatchingEntropyBounds
-- name    : MatchingEntropyBounds
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:18.365732+00:00
-- url     : https://prove2.me/theorems/1d6c552a-afaf-41ad-ae15-e54d61523cd5
-- statement:
--   A loopless graph on a finite vertex type V with finite edge type E is given by two endpoint maps left and right from E to V, with left e ≠ right e for every edge e, so parallel edges are allowed but loops are not. An edge e is incident to v if v is one of its endpoints. A perfect matching is a finite set M of edges such that every vertex is incident to exactly one edge of M, and Matching(G) is the finite type of such matchings. The indicator of a matching M is the function on edges equal to 1 on edges of M and 0 elsewhere. The polytope of G is the convex hull in ℝ^E of all these indicator vectors. For a weight function p on matchings, mean(p) is the edge vector with e-th coordinate Σ_M p(M)·1[e ∈ M]. The probabilitySimplex of an index type is the set of nonnegative weights summing to 1, and feasibleLaws(G,y) is the set of probability distributions p on perfect matchings whose mean equals a target edge vector y. The entropy of a finite weight function p is Σ_i negMulLog(p_i), that is, the Shannon entropy Σ −p_i log p_i with the convention 0·log 0 = 0, and maxMatchingEntropy(G,y) is the supremum of this entropy over feasibleLaws(G,y); as a real supremum it equals 0 if the feasible set is empty, for instance when y lies outside the polytope. Finally, complementEntropy(x), in the Refined namespace, is the entropy of the complementary vector e ↦ 1 − x(e). The block only sets up these definitions and states no bounds or theorems.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MatchingEntropyBounds.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MatchingEntropyBounds.lean; bytes 16..2081
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uIndex uι

namespace MatchingEntropyBounds

structure LooplessGraph (V : Type uV) (E : Type uE) where
  left : E → V
  right : E → V
  loopless : ∀ e, left e ≠ right e

variable {V : Type uV} {E : Type uE}
  [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

def Incident (G : LooplessGraph V E) (v : V) (e : E) : Prop :=
  G.left e = v ∨ G.right e = v

instance incidentDecidable (G : LooplessGraph V E) (v : V) (e : E) :
    Decidable (G.Incident v e) := inferInstanceAs (Decidable (G.left e = v ∨ G.right e = v))

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

end LooplessGraph

def probabilitySimplex (Index : Type uIndex) [Fintype Index] : Set (Index → ℝ) :=
  {weights | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1}

def LooplessGraph.feasibleLaws (G : LooplessGraph V E) (y : E → ℝ) : Set (G.Matching → ℝ) :=
  {p | p ∈ probabilitySimplex G.Matching ∧ G.mean p = y}

def entropy {ι : Type uι} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

def maxMatchingEntropy (G : LooplessGraph V E) (y : E → ℝ) : ℝ :=
  sSup (entropy '' G.feasibleLaws y)

namespace Refined

def complementEntropy (x : E → ℝ) : ℝ := entropy (fun e => 1 - x e)

end Refined

open Module Matrix

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

open LooplessGraph



end MatchingEntropyBounds
end
end OAI


