-- Prove2me | Definitions.Def_Menger_Linkage
-- name    : Menger_Linkage
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-06T13:09:43.392114+00:00
-- url     : https://prove2.me/theorems/4744829f-ac30-4e73-8b8e-3b72484a9ba9
-- title:
--   Paths, separators and linkages for Menger's theorem
-- statement:
--   Let $G$ be a graph and $S, A, B$ finite sets of vertices. An **$A$–$B$ path inside $S$** is a nonempty list of distinct vertices of $S$, consecutive entries adjacent in $G$, whose first vertex is in $A$ and whose last vertex is in $B$ (a single vertex of $A\cap B$ is allowed). A set $X$ of vertices is an **$A$–$B$ separator inside $S$** if every $A$–$B$ path inside $S$ contains a vertex of $X$. A **linkage of size $k$** is a family of $k$ pairwise vertex-disjoint $A$–$B$ paths inside $S$. These notions are the data of the set form of Menger's theorem: the maximum size of a linkage equals the minimum size of a separator.
-- source:
--   R. Diestel, Graph Theory, 5th ed., Section 3.3, Theorem 3.3.1 (Menger 1927) and the definitions preceding it.

import Mathlib

namespace Menger

variable {V : Type*}

/-- A path of `G` inside the vertex set `S`, listed from a vertex of `A` to a vertex of `B`: a
nonempty duplicate-free list of vertices of `S`, consecutive entries adjacent, whose first entry
lies in `A` and whose last entry lies in `B`. -/
def IsABPath (G : SimpleGraph V) (S A B : Finset V) (p : List V) : Prop :=
  p ≠ [] ∧ p.Nodup ∧ List.IsChain G.Adj p ∧ (∀ v ∈ p, v ∈ S) ∧
    (∃ a, p.head? = some a ∧ a ∈ A) ∧ (∃ b, p.getLast? = some b ∧ b ∈ B)

/-- `X` is an `A`–`B` separator inside `S`: it meets every `A`–`B` path of `G` inside `S`. -/
def IsABSep (G : SimpleGraph V) (S A B X : Finset V) : Prop :=
  ∀ p, IsABPath G S A B p → ∃ x ∈ X, x ∈ p

/-- There are `k` pairwise vertex-disjoint `A`–`B` paths of `G` inside `S`. -/
def HasLinkage (G : SimpleGraph V) (S A B : Finset V) (k : ℕ) : Prop :=
  ∃ L : List (List V), L.length = k ∧ (∀ p ∈ L, IsABPath G S A B p) ∧
    L.Pairwise (fun p q => ∀ v ∈ p, v ∉ q)

end Menger


