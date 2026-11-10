-- Prove2me | Definitions.Def_RandTreeUniv_IsPathSystemIn
-- name    : RandTreeUniv_IsPathSystemIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:10:13.262462+00:00
-- url     : https://prove2.me/theorems/739323e5-2909-4632-bc4a-ec8db7c81c52
-- title:
--   $G[S]$ contains an $(\mathbf a,\mathbf b;k)$-path system (Definition 3.1)
-- statement:
--   Let $G$ be a graph, $S$ a set of its vertices, $k\ge0$ an integer, and $\mathbf a=(a_1,\dots,a_m)$, $\mathbf b=(b_1,\dots,b_m)$ two $m$-tuples of vertices. We say that **$G[S]$ contains an $(\mathbf a,\mathbf b;k)$-path system** if there are paths $P_1,\dots,P_m$ in $G$ such that
--
--   1. $P_i$ is a path from $a_i$ to $b_i$ with exactly $k$ edges;
--   2. every vertex of every $P_i$ lies in $S$;
--   3. the paths are pairwise vertex-disjoint.
--
--   A path system is a vertex-disjoint union of paths; it is an $(\mathbf a,\mathbf b;k)$-path system when it has $m$ components, each a path of length $k$ joining $a_i$ to $b_i$. With $S$ the whole vertex set this is "$G$ contains an $(\mathbf a,\mathbf b;k)$-path system". Path systems are the building block of linking systems.
--
--   **Formalization Note** The length of a path is its number of edges. Distinctness and disjointness of the tuples are hypotheses of the theorems that use this predicate.
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), §2.1, p.9 (PDF 10) and Definition 3.1, p.13 (PDF 14)

import Mathlib

set_option autoImplicit false

open scoped Classical

namespace RandTreeUniv

/-- `G[S]` contains an `(a, b; k)`-path system (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), §2.1, p.9 (PDF 10) and Definition 3.1,
p.13 (PDF 14)): there are `m` pairwise vertex-disjoint paths of `G`, the `i`-th one an
`a_i b_i`-path of length exactly `k` (number of edges), all of whose vertices lie in `S`.

**Formalization Note** The tuples are maps `a b : Fin m → V`. A path system is a subgraph whose
components are the paths, so it is recorded by the `m` paths themselves; vertex-disjointness
makes them the components. "`G[S]` contains" means the paths use only vertices of `S`; take
`S = Set.univ` for `G` itself. The paper's standing assumptions on the tuples (distinct entries,
`a`, `b` disjoint) are hypotheses of the theorems, not part of this predicate. -/
def IsPathSystemIn {V : Type*} (G : SimpleGraph V) (S : Set V) {m : ℕ} (a b : Fin m → V)
    (k : ℕ) : Prop :=
  ∃ P : ∀ i, G.Walk (a i) (b i),
    (∀ i, (P i).IsPath ∧ (P i).length = k ∧ ∀ v ∈ (P i).support, v ∈ S) ∧
    ∀ i j, i ≠ j → ∀ v ∈ (P i).support, v ∉ (P j).support

end RandTreeUniv


