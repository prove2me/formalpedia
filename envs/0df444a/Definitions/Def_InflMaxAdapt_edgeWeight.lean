-- Prove2me | Definitions.Def_InflMaxAdapt_edgeWeight
-- name    : InflMaxAdapt_edgeWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:32:40.383921+00:00
-- url     : https://prove2.me/theorems/933adda9-274b-48d6-8c52-da7156675e1f
-- title:
--   Law of the live undirected edge set
-- statement:
--   In the **undirected-edge representation** each unordered pair $e = \{u, v\}$ of vertices is a live edge independently with probability $q_e \in [0,1]$; the random set $A$ of live edges has the law
--   $$
--   \mathbb P(A = E) \;=\; \prod_{e \in E} q_e \prod_{e \notin E} (1 - q_e) .
--   $$
--   This is independent bond percolation on the complete graph on $V$ with edge probabilities $q$.
--
--   **Formalization Note** The pairs $\{v, v\}$ are included among the potential edges; they never change which vertices are connected. The constraint $q \in [0,1]$ is a hypothesis of the theorems.
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Section 2, printed p.5 (PDF p.6), and footnote 3

import Mathlib

namespace InflMaxAdapt

/-- The law of the random set of live undirected edges (Section 2 and footnote 3, printed p.5 =
PDF p.6, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)): every unordered pair `e = {u, v}` is live independently with probability `q_e`,
so `P(A = E) = ∏_{e ∈ E} q_e · ∏_{e ∉ E} (1 − q_e)`.

**Formalization Note** Pairs are `Sym2 V`; the diagonal pairs `s(v, v)` are included as potential
edges but never affect connectivity (`SimpleGraph.fromEdgeSet` drops loops). The constraint
`q ∈ [0,1]` is a hypothesis of the theorems. -/
def edgeWeight {V : Type} [Fintype V] [DecidableEq V] (q : Sym2 V → ℝ) (E : Finset (Sym2 V)) : ℝ :=
  (∏ e ∈ E, q e) * ∏ e ∈ Finset.univ \ E, (1 - q e)

end InflMaxAdapt


