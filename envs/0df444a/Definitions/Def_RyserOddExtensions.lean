-- Prove2me | Definitions.Def_RyserOddExtensions
-- name    : RyserOddExtensions
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:17.603162+00:00
-- url     : https://prove2.me/theorems/554c3370-bd14-4da1-a496-10c3086343ad
-- statement:
--   A hypergraph on a vertex type is a finite set of finite vertex sets (edges). A cover is a finite vertex set meeting every edge; a hypergraph is Intersecting if any two distinct edges share a vertex. A matching is a subfamily of pairwise disjoint edges, matchingNumber is the largest size of a matching (the supremum of the cardinalities of all matchings), and coverNumber is the least cardinality of a cover (the infimum of the set of cover sizes, which is 0 by convention if no cover exists). Uniform(r) says every edge has exactly r vertices, and PartiteUniform for a labelling part of vertices by an index type says every edge contains exactly one vertex with each label; RPartiteUniform(r) means that some labelling of the vertices by Fin r makes the hypergraph partite-uniform in this sense. The defined proposition Specification.ExplicitFailureAt(r) asserts that there exist a finite vertex type (in the lowest universe, with decidable equality) and a nonempty hypergraph on it such that r>0, the hypergraph is r-partite and r-uniform, intersecting, admits a cover, has matchingNumber equal to 1 and coverNumber equal to r, and satisfies (r−1)·matchingNumber < coverNumber. Given the other conditions this final inequality reads r−1<r, so it holds automatically for positive r; the proposition is a defined statement of a Ryser-type counterexample for rank r, not an established theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/RyserOddExtensions.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/RyserOddExtensions.lean; bytes 16..2386
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample

abbrev Hypergraph (Vertex : Type*) := Finset (Finset Vertex)

variable {Vertex : Type*} [DecidableEq Vertex]

def IsCover (hypergraph : Hypergraph Vertex) (cover : Finset Vertex) : Prop :=
  ∀ edge ∈ hypergraph, ∃ vertex ∈ cover, vertex ∈ edge

def Intersecting (hypergraph : Hypergraph Vertex) : Prop :=
  ∀ edge ∈ hypergraph, ∀ other ∈ hypergraph, edge ≠ other → (edge ∩ other).Nonempty

attribute [-instance] instDecidablePairwiseCoeFinsetOfDecidableEqOfDecidableRel in
def matchings (hypergraph : Hypergraph Vertex) : Finset (Hypergraph Vertex) := by
  classical
  exact hypergraph.powerset.filter fun matching =>
    (matching : Set (Finset Vertex)).Pairwise Disjoint

def matchingNumber (hypergraph : Hypergraph Vertex) : ℕ :=
  (matchings hypergraph).sup Finset.card

def coverCardinalities (hypergraph : Hypergraph Vertex) : Set ℕ :=
  {size | ∃ cover : Finset Vertex, IsCover hypergraph cover ∧ cover.card = size}

def coverNumber (hypergraph : Hypergraph Vertex) : ℕ := sInf (coverCardinalities hypergraph)

def Uniform (rank : ℕ) (hypergraph : Hypergraph Vertex) : Prop :=
  ∀ edge ∈ hypergraph, edge.card = rank

def PartiteUniform {Index : Type*} (part : Vertex → Index)
    (hypergraph : Hypergraph Vertex) : Prop :=
  ∀ edge ∈ hypergraph, ∀ index : Index,
    ∃! vertex : Vertex, vertex ∈ edge ∧ part vertex = index

def RPartiteUniform (rank : ℕ) (hypergraph : Hypergraph Vertex) : Prop :=
  ∃ part : Vertex → Fin rank, PartiteUniform part hypergraph

end RyserCoveringCounterexample

namespace RyserOdd

open RyserCoveringCounterexample

def Specification.ExplicitFailureAt (rank : ℕ) : Prop :=
  ∃ (Vertex : Type) (finiteVertices : Fintype Vertex) (decidableVertices : DecidableEq Vertex),
    letI : Fintype Vertex := finiteVertices
    letI : DecidableEq Vertex := decidableVertices
    ∃ hypergraph : RyserCoveringCounterexample.Hypergraph Vertex,
      0 < rank ∧ hypergraph.Nonempty ∧ RPartiteUniform rank hypergraph ∧
        Uniform rank hypergraph ∧ Intersecting hypergraph ∧
        (∃ cover : Finset Vertex, IsCover hypergraph cover) ∧
        matchingNumber hypergraph = 1 ∧ coverNumber hypergraph = rank ∧
        (rank - 1) * matchingNumber hypergraph < coverNumber hypergraph



end RyserOdd
end
end OAI


