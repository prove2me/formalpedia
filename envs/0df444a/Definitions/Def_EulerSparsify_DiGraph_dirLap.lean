-- Prove2me | Definitions.Def_EulerSparsify_DiGraph_dirLap
-- name    : EulerSparsify_DiGraph_dirLap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:34:02.043465+00:00
-- url     : https://prove2.me/theorems/22104084-feed-4b12-97f5-86a9985f25ca
-- title:
--   Directed Laplacian $\vec L=B^\top WH$
-- statement:
--   The **directed Laplacian** of $\vec G=(V,E,w)$ is
--
--   $$\vec L_{\vec G}=B^\top W H,$$
--
--   where $H$ indicates the heads (sources) of the edges. For a single edge $0\to1$ of weight $1$ this is $\begin{pmatrix}1&0\\-1&0\end{pmatrix}$, and $\vec L^\top\mathbf 1=0$ for every graph.
--
--   **Formalization Note** The head is the source (footnote 1, p.8); exchanging $H$ and $T$ would give the Laplacian of the reversed graph.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), §3, Graph matrices, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_EulerSparsify_DiGraph_lap

namespace EulerSparsify

/-- **Directed Laplacian** `⃗L = BᵀWH` (§3, "Graph matrices", p.9, PDF p.11).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), §3, p.9: "For directed
⃗G = (V, E, w), its directed Laplacian is ⃗L := BᵀWH."

**Formalization Note.** `H` indicates the heads, which are the sources (footnote 1, p.8). For a
single edge `0 → 1` of weight 1 this gives `⃗L = [[1, 0], [−1, 0]]` (checked in
`Solutions/verification/EulerSparsify_sanity.lean`). -/
noncomputable def DiGraph.dirLap {V E : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : DiGraph V E) : Matrix V V ℝ :=
  G.incMat.transpose * G.wMat * G.Hmat

end EulerSparsify


