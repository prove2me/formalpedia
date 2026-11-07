-- Prove2me | Definitions.Def_MinrankTW_supportGraph
-- name    : MinrankTW_supportGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:49.440708+00:00
-- url     : https://prove2.me/theorems/bfcbab6a-e741-4a1f-bb68-7f80397ae7e9
-- title:
--   Bipartite support graph of entry constraints
-- statement:
--   The **bipartite support graph** of entry constraints $S=(S_{ij})_{i\in[m],j\in[n]}$ has vertex set $\{r_1,\dots,r_m\}\,\dot\cup\,\{c_1,\dots,c_n\}$ (one vertex per row and one per column) and edge set
--   $$
--   E=\{r_ic_j : S_{ij}\setminus\{0\}\neq\emptyset\}.
--   $$
--   An edge marks an entry that is allowed to be nonzero, including a fixed nonzero entry; an entry with $S_{ij}=\{0\}$ is not an edge. There are no row–row or column–column edges.
--
--   Theorem 2 is parameterized by the width of a tree decomposition of this graph.
--
--   **Formalization Note** Row $r_i$ is `Sum.inl i` and column $c_j$ is `Sum.inr j`.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Section 1.2, p.5

import Mathlib

namespace MinrankTW

/-- The **bipartite support graph** of the entry constraints `S` (Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), §1.2, p.5):
vertices `{r_1, …, r_m} ∪̇ {c_1, …, c_n}` and edges `{r_i c_j : S_ij ∖ {0} ≠ ∅}`.

**Formalization Note** Row vertex `r_i` is `Sum.inl i` and column vertex `c_j` is
`Sum.inr j`. An edge `r_i c_j` is present exactly when `S_ij` contains a nonzero element (a
fixed nonzero entry is an edge, `S_ij = {0}` is not). There are no row–row or column–column
edges; `SimpleGraph.fromRel` symmetrizes the relation. -/
def supportGraph {F : Type*} [Zero F] {m n : ℕ} (S : Fin m → Fin n → Finset F) :
    SimpleGraph (Fin m ⊕ Fin n) :=
  SimpleGraph.fromRel fun u v => ∃ i j, u = Sum.inl i ∧ v = Sum.inr j ∧ ∃ a ∈ S i j, a ≠ 0

end MinrankTW


