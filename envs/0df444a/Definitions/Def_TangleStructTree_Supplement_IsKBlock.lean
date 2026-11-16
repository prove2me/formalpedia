-- Prove2me | Definitions.Def_TangleStructTree_Supplement_IsKBlock
-- name    : TangleStructTree_Supplement_IsKBlock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:09:33.599235+00:00
-- url     : https://prove2.me/theorems/df9c717b-987c-4b2d-b03b-a507f4ae9a2b
-- title:
--   $k$-blocks
-- statement:
--   Let $G$ be a finite graph and $k\in\mathbb N$. A set $Z$ of vertices **separates** two vertices $a,b$ if $a,b\notin Z$ and every $a$–$b$ path in $G$ meets $Z$. A **$k$-block** of $G$ is a maximal set $X$ of at least $k$ vertices no two of which can be separated by fewer than $k$ vertices:
--
--   1. $|X|\ge k$;
--   2. no two distinct $a,b\in X$ are separated by any $Z$ with $|Z|<k$;
--   3. no proper superset of $X$ has properties 1 and 2.
--
--   **Formalization Note** Every $a$–$b$ walk contains an $a$–$b$ path, so the separation condition is stated for walks.
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), §7, p.21 (PDF 32): k-block; separation of vertices as in [11]

import Mathlib

namespace TangleStructTree

namespace Supplement

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A set `Z` of vertices **separates** two vertices `a, b` of `G` if `a, b ∉ Z` and every `a`–`b`
path in `G` meets `Z` ([11], §1.4, the terminology adopted by von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §3, p.6).

**Formalization Note** Every `a`–`b` walk contains an `a`–`b` path, so quantifying over walks is
the same condition. -/
def SeparatesVertices (G : SimpleGraph V) (Z : Finset V) (a b : V) : Prop :=
  a ∉ Z ∧ b ∉ Z ∧ ∀ p : G.Walk a b, ∃ z ∈ Z, z ∈ p.support

/-- No two (distinct) vertices of `X` can be separated by fewer than `k` vertices. -/
def IsKInseparable (G : SimpleGraph V) (k : ℕ) (X : Finset V) : Prop :=
  ∀ a ∈ X, ∀ b ∈ X, a ≠ b → ∀ Z : Finset V, Z.card < k → ¬ SeparatesVertices G Z a b

/-- "For any `k ∈ ℕ`, a **`k`-block** in a graph is any maximal set of at least `k` vertices no two
of which can be separated by `< k` vertices" (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §7, p.21 (PDF 32)).

**Formalization Note** Maximality is among all vertex sets with at least `k` vertices no two of
which can be separated by fewer than `k` vertices. -/
def IsKBlock (G : SimpleGraph V) (k : ℕ) (X : Finset V) : Prop :=
  k ≤ X.card ∧ IsKInseparable G k X ∧
    ∀ Y : Finset V, X ⊆ Y → k ≤ Y.card → IsKInseparable G k Y → Y = X

end Supplement

end TangleStructTree


