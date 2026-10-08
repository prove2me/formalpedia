-- Prove2me | Definitions.Def_StrongThinTree
-- name    : StrongThinTree
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:26.867577+00:00
-- url     : https://prove2.me/theorems/74f101a5-e4cd-408d-a1cc-d9282723f839
-- statement:
--   A MultiGraph on n vertices (Fin n) with m edges (Fin m) assigns each edge e a left endpoint and a right endpoint, both vertices, required to be different, so there are no loops but parallel edges are allowed. For a set T of edges and a vertex set S, cut(T,S) is the set of edges of T with exactly one endpoint in S. Connected(T) means that every nonempty proper subset S of the vertices is crossed by at least one edge of T. SpanningTree(T) means T is Connected and is minimal with this property: removing any single edge of T destroys connectedness. EdgeConnected(k) means that every nonempty proper vertex subset S is crossed by at least k edges of the whole edge set, that is, |cut(univ,S)| ≥ k. MainStatement is a defined proposition, not an established theorem. It asserts that there is a real constant C>0 such that for every integer k≥1, every n≥2 and every m, and every multigraph G on n vertices and m edges that is k-edge-connected, there exists a spanning tree T of G such that for every nonempty proper vertex subset S, the number of tree edges crossing S is at most (C/k) times the number of edges of G crossing S.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/StrongThinTree.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/StrongThinTree.lean; bytes 16..1276
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace StrongThinTree

structure MultiGraph (n m : ℕ) where
  left : Fin m → Fin n
  right : Fin m → Fin n
  loopless : ∀ e, left e ≠ right e

namespace MultiGraph

def cut {n m : ℕ} (G : MultiGraph n m) (T : Finset (Fin m))
    (S : Finset (Fin n)) : Finset (Fin m) :=
  T.filter fun e => (G.left e ∈ S ∧ G.right e ∉ S) ∨
    (G.right e ∈ S ∧ G.left e ∉ S)

def Connected {n m : ℕ} (G : MultiGraph n m) (T : Finset (Fin m)) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ → (G.cut T S).Nonempty

def SpanningTree {n m : ℕ} (G : MultiGraph n m) (T : Finset (Fin m)) : Prop :=
  G.Connected T ∧ ∀ e ∈ T, ¬ G.Connected (T.erase e)

def EdgeConnected {n m : ℕ} (G : MultiGraph n m) (k : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
    k ≤ (G.cut Finset.univ S).card

end MultiGraph

def MainStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (n m : ℕ), 2 ≤ n →
    ∀ G : MultiGraph n m, G.EdgeConnected k →
      ∃ T : Finset (Fin m), G.SpanningTree T ∧
        ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
          ((G.cut T S).card : ℝ) ≤ (C / (k : ℝ)) * (G.cut Finset.univ S).card



end StrongThinTree
end OAI


