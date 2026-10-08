-- Prove2me | Definitions.Def_BalancedRyser
-- name    : BalancedRyser
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:00.904704+00:00
-- url     : https://prove2.me/theorems/c78e4e14-3799-44c8-9b37-f5586c651986
-- statement:
--   For nonnegative integers r and n, a PartiteHypergraph consists of a finite set of edges, each choosing exactly one of n vertices from each of r disjoint vertex classes; its vertices are pairs (i,v) with 0≤i<r and 0≤v<n. A finite vertex set C covers the hypergraph when every edge contains at least one vertex of C. The hypergraph is Intersecting when it has at least one edge and every two edges have a common vertex, and Nonisolated when every vertex lies in some edge. It has cover number k when a cover of exactly k vertices exists and every cover has at least k vertices. BalancedCounterexample(q) is the defined proposition that there exists an intersecting, nonisolated hypergraph with q+1 vertex classes, each containing q+1 vertices, whose cover number is q+1. MainResult is the defined proposition that such a hypergraph exists for every sufficiently large prime q: there is a nonnegative integer q₀ such that every prime q≥q₀ satisfies BalancedCounterexample(q).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BalancedRyser.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BalancedRyser.lean; bytes 16..1086
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace Balanced
open scoped _root_.Balanced

structure PartiteHypergraph (r n : ℕ) where
  edges : Finset (Fin r → Fin n)

namespace PartiteHypergraph

variable {r n : ℕ}

abbrev Vertex (r n : ℕ) := Fin r × Fin n

def Covers (H : PartiteHypergraph r n) (C : Finset (Vertex r n)) : Prop :=
  ∀ e ∈ H.edges, ∃ i, (i, e i) ∈ C

def Intersecting (H : PartiteHypergraph r n) : Prop :=
  H.edges.Nonempty ∧ ∀ e ∈ H.edges, ∀ f ∈ H.edges, ∃ i, e i = f i

def Nonisolated (H : PartiteHypergraph r n) : Prop :=
  ∀ i v, ∃ e ∈ H.edges, e i = v

def HasCoverNumber (H : PartiteHypergraph r n) (k : ℕ) : Prop :=
  (∃ C : Finset (Vertex r n), H.Covers C ∧ C.card = k) ∧
    ∀ C : Finset (Vertex r n), H.Covers C → k ≤ C.card

end PartiteHypergraph

def BalancedCounterexample (q : ℕ) : Prop :=
  ∃ H : PartiteHypergraph (q + 1) (q + 1),
    H.Intersecting ∧ H.Nonisolated ∧ H.HasCoverNumber (q + 1)

def MainResult : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → q.Prime → BalancedCounterexample q



end Balanced
end OAI


