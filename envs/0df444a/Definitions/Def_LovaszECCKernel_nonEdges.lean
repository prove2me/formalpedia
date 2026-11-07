-- Prove2me | Definitions.Def_LovaszECCKernel_nonEdges
-- name    : LovaszECCKernel_nonEdges
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:54:43.100592+00:00
-- url     : https://prove2.me/theorems/50f79988-5eac-46dc-9bf0-b89c8412e33f
-- title:
--   Non-edges $\overline E(G)$ and the edge count $m=|E(G)|$
-- statement:
--   For a finite simple graph $G$, the **non-edges** are the pairs of distinct vertices that are not adjacent:
--   $$\overline E(G)=\binom{V(G)}{2}\setminus E(G)=E(\overline G),$$
--   where $\overline G$ is the complement of $G$. Its size $\bar m=|\overline E(G)|=\binom{n}{2}-m$ enters Lovász's bound. The **edge count** $m=|E(G)|$ is the number of edges; running times of the paper are measured in $n+m$.
--
--   **Formalization Note** Unordered pairs are `Sym2 V`; $\overline E(G)$ is the edge set of Mathlib's complement graph, so it never contains a diagonal pair. Decidability of adjacency is classical.
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), §2, p.15 (= PDF p.15), and p.4 (= PDF p.4)

import Mathlib

set_option autoImplicit false

namespace LovaszECCKernel

/-- The **non-edges** `E̅(G) = (V(G) choose 2) \ E(G) = E(G̅)` of a finite simple graph
(Fomin, Golovach, Khargeliia, Sagunov, Simonov, *Stability Meets Kernelization: Algorithmic
Extensions of the Lovász and Erdős–Goodman–Pósa Theorems*, STOC 2027 submission (manuscript
sha256 a9d53ab8…), §2, p.15 (= PDF p.15)): "We write (V(G) choose 2) to denote the set of all
pairs of distinct vertices. The complement G̅ of a graph G has the same set of vertices as G and
two distinct vertices u, v ∈ V(G) are adjacent in G̅ if and only if they are non-neighbors in G;
we write E̅(G) = (V(G) choose 2) \ E(G) to denote E(G̅)."

**Formalization Note** Unordered pairs are `Sym2 V`; `E̅(G)` is the edge set of Mathlib's
complement `Gᶜ`, so it contains no diagonal pair `s(v, v)`. Decidability is classical. -/
noncomputable def nonEdges {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset (Sym2 V) := by
  classical exact Gᶜ.edgeFinset

/-- The number `m = |E(G)|` of edges of a finite simple graph (Fomin et al., STOC 2027 submission
(manuscript sha256 a9d53ab8…), p.4 (= PDF p.4): "m denotes the number of edges in G").

**Formalization Note** Decidability of adjacency is classical. -/
noncomputable def edgeCount {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ := by
  classical exact G.edgeFinset.card

end LovaszECCKernel


