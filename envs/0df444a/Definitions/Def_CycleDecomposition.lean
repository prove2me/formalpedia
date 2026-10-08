-- Prove2me | Definitions.Def_CycleDecomposition
-- name    : CycleDecomposition
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:06.762205+00:00
-- url     : https://prove2.me/theorems/86edfe64-00da-4886-8ea9-de3dc5490ddb
-- statement:
--   For a simple graph G on a vertex type V, CycleOrSingleEdge(G,s) means that the set s of unordered vertex pairs is either the edge set of a closed walk that is a simple cycle in G, or a singleton containing one edge of G. EdgeDecomposition(G,k), for a nonnegative integer k, means that there is an indexed family of k such sets whose members are pairwise disjoint and whose union is the entire edge set of G. Thus each edge belongs to exactly one part, and each part is a cycle or a single edge. MainStatement is the defined proposition that there exists a positive real constant C such that, for every nonnegative integer n and every simple graph G on the n vertices indexed by Fin n, there is a nonnegative integer k for which EdgeDecomposition(G,k) holds and k ≤ Cn. The same constant C must work for all n and all such graphs.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CycleDecomposition.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CycleDecomposition.lean; bytes 16..768
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section


open Filter Asymptotics Real
open scoped Topology

open MeasureTheory ProbabilityTheory Finset

namespace ErdosGallai

def CycleOrSingleEdge {V : Type} (G : SimpleGraph V)
    (s : Set (Sym2 V)) : Prop :=
  (∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ s = p.edgeSet) ∨
  ∃ e ∈ G.edgeSet, s = {e}

def EdgeDecomposition {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ parts : Fin k → Set (Sym2 V),
    (∀ i, CycleOrSingleEdge G (parts i)) ∧
    Pairwise (fun i j => Disjoint (parts i) (parts j)) ∧
    (⋃ i, parts i) = G.edgeSet


def MainStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    ∃ k : ℕ, EdgeDecomposition G k ∧ (k : ℝ) ≤ C * n



end ErdosGallai
end
end OAI


