-- Prove2me | Definitions.Def_GeoSemialgCSP_cousins
-- name    : GeoSemialgCSP_cousins
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:46:55.306818+00:00
-- url     : https://prove2.me/theorems/3e1cc1fe-0db7-475c-81f6-7717526dcc5a
-- title:
--   The cousins predicate on the ordered $k$-ary tree
-- statement:
--   In an ordered rooted tree in which every node has children numbered $0,\dots,k-1$, nodes $l_1,\dots,l_k$ are **cousins** if they have a common ancestor $u$ such that $l_i$ lies in the subtree rooted at the $i$-th child of $u$, for every $i$.
--
--   The cousins predicate is the template predicate of the multiscale instance; a predicate with a cousins homomorphism inherits its hardness.
--
--   **Formalization Note** The predicate is stated on the universal ordered $k$-ary tree, whose nodes are the finite words over $\{0,\dots,k-1\}$: the $i$-th child of $u$ is $u\,i$, and $v$ lies below $w$ iff $w$ is a prefix of $v$. Every finite ordered $k$-ary tree embeds in it preserving the predicate. Children are numbered from $0$ (the paper's $1,\dots,k$).
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3 Assumptions, p.7 (PDF p.8)

import Mathlib

namespace GeoSemialgCSP

/-- **The cousins predicate.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3 Assumptions, printed p.7 (PDF p.8):
`cousins(l₁, …, l_k) = 1` iff there is a common ancestor `u` of the `lᵢ` such that `lᵢ` lies in
the subtree rooted at the `i`-th child of `u` (the tree is ordered).

**Formalization Note.** Stated on the universal ordered `k`-ary tree: nodes are words
`List (Fin k)`, the `i`-th child of `u` is `u ++ [i]`, and `v` is in the subtree of `w` iff `w` is
a prefix of `v`. Children are 0-based (`Fin k`), the paper's 1..k. Every finite ordered `k`-ary
tree embeds in this tree preserving the predicate. -/
def cousins {k : ℕ} (l : Fin k → List (Fin k)) : Prop :=
  ∃ u : List (Fin k), ∀ i, (u ++ [i]) <+: l i

end GeoSemialgCSP


