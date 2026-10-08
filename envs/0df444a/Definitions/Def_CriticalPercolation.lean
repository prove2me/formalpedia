-- Prove2me | Definitions.Def_CriticalPercolation
-- name    : CriticalPercolation
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:06.139025+00:00
-- url     : https://prove2.me/theorems/a40e7d91-b138-4017-8eb1-2a72c321bcca
-- statement:
--   A bond graph consists of a vertex set V, a set E of labelled bonds, and an assignment of an unordered pair of endpoints to each bond; loops and parallel bonds are allowed. For a retained set ω ⊆ E, its open graph is the simple graph determined by those bonds, discarding loops and merging parallel connections. The full graph retains every bond. Local finiteness means that each vertex belongs to only finitely many labelled bonds, counting multiplicities. An automorphism consists of bijections of both vertices and bonds that preserve the unordered endpoints. Quasi-transitivity means that finitely many vertices represent all vertex orbits under these automorphisms. The open cluster of v is the set of vertices reachable from v by finite paths in the open graph, including v itself via the path of length zero. The percolation event consists of retained-bond sets for which at least one such cluster is infinite. For each p ∈ [0,1], the percolation law independently retains every labelled bond with probability p. The critical probability is the infimum, taken in [0,1], of the parameters p for which the percolation event has strictly positive probability. These constructions do not require local finiteness or quasi-transitivity; those are separately defined properties.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CriticalPercolation.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CriticalPercolation.lean; bytes 16..1835
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open Set MeasureTheory ProbabilityTheory

namespace CriticalPercolation

/-- An undirected graph with labelled bonds, including loops and parallel bonds. -/
structure BondGraph (V E : Type*) where
  ends : E → Sym2 V

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

/-- The graph of retained bonds. `fromEdgeSet` discards loops. -/
def openGraph (ω : Set E) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (G.ends '' ω)

/-- The underlying connectivity graph with every bond retained. -/
def fullGraph : SimpleGraph V := G.openGraph Set.univ

/-- Local finiteness counts bonds, not just distinct neighbors. -/
def LocallyFinite : Prop := ∀ v : V, {e : E | v ∈ G.ends e}.Finite

/-- Automorphisms preserve the vertex and bond structure, including multiplicities. -/
structure Aut where
  vertex : V ≃ V
  edge : E ≃ E
  preserves : ∀ e, G.ends (edge e) = Sym2.map vertex (G.ends e)

/-- Finitely many vertex orbits under the full automorphism group. -/
def QuasiTransitive : Prop :=
  ∃ S : Set V, S.Finite ∧ ∀ v : V, ∃ s ∈ S, ∃ φ : G.Aut, φ.vertex s = v

/-- Finite open paths, including the path of length zero, define the open cluster. -/
def cluster (ω : Set E) (v : V) : Set V := {w | (G.openGraph ω).Reachable v w}

/-- The event that at least one open cluster is infinite. -/
def percolates : Set (Set E) := {ω | ∃ v : V, (G.cluster ω v).Infinite}

/-- Independent retention with parameter `p ∈ [0,1]` of each labelled bond. -/
noncomputable def law (_G : BondGraph V E) (p : unitInterval) : Measure (Set E) :=
  ProbabilityTheory.setBernoulli Set.univ p

/-- The infimum of parameters with positive probability of an infinite cluster. -/
noncomputable def criticalProbability : unitInterval :=
  sInf {p : unitInterval | 0 < G.law p G.percolates}



end BondGraph
end CriticalPercolation
end OAI


