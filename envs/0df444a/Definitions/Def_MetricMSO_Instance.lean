-- Prove2me | Definitions.Def_MetricMSO_Instance
-- name    : MetricMSO_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:16.956934+00:00
-- url     : https://prove2.me/theorems/2c0b8565-a3e2-4598-9267-2915f3a7c0b6
-- title:
--   Graph with unary input predicates on vertices and edges
-- statement:
--   An **instance** consists of a finite simple undirected graph $G$ on the vertex set $\{0,\dots,n-1\}$ together with unary input predicates: $q$ subsets $L_1,\dots,L_q\subseteq V(G)$ and $q'$ subsets of $E(G)$. The predicates may overlap, and they are fixed by the instance: they are not among the choices that an algorithm optimizes or counts.
--
--   Every formula of the mission is evaluated on such an instance.
--
--   **Formalization Note** Vertices are `Fin n` and edges are elements of `G.edgeSet` inside `Sym2 (Fin n)`. A CMSO1 formula simply never mentions the edge predicates.
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), §2.1, p.12 (PDF 14); §2.7, p.16 (PDF 18)

import Mathlib

namespace MetricMSO

/-- **An instance: a finite simple graph with unary input predicates on vertices and on edges.**

Chakraborty, Ordyniak, Siebertz, *Model Checking for Metric Extensions of Monadic Second-Order
Logic* (arXiv:2610.41974, sha256 prefix ad3c5863), §2.1, p.12 (PDF 14): "All graphs we consider are
finite, simple, and undirected"; §2.7, p.16 (PDF 18): "The unary input predicates L1, . . . , Lq
describe given subsets of V(G) … These input sets may overlap … When we work with incidence
structures, we may also have unary input predicates on edge elements."

An instance consists of
* `n`, the number of vertices; the vertex set is `Fin n`;
* `G`, a simple graph on `Fin n`;
* `q` vertex predicates `vpred j ⊆ V(G)` (`j < q`), which may overlap;
* `q'` edge predicates `epred j ⊆ E(G)` (`j < q'`), which may overlap.

**Formalization Note** Vertices are `Fin n`; an edge is an element of `G.edgeSet ⊆ Sym2 (Fin n)`.
The edge predicates are subsets of `E(G)` (`epred_sub`). Formulas of CMSO1 simply never mention
the edge predicates. -/
structure Instance where
  n : ℕ
  G : SimpleGraph (Fin n)
  q : ℕ
  vpred : Fin q → Finset (Fin n)
  q' : ℕ
  epred : Fin q' → Finset (Sym2 (Fin n))
  epred_sub : ∀ j, ∀ e ∈ epred j, e ∈ G.edgeSet

end MetricMSO


