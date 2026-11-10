-- Prove2me | Definitions.Def_LEDPCount_subgraphCount
-- name    : LEDPCount_subgraphCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:06:58.843891+00:00
-- url     : https://prove2.me/theorems/c4cfab6c-9432-4bba-ad97-1b8def1c9dfe
-- title:
--   Adjacency matrix $A$ and subgraph count $f_H(G)$
-- statement:
--   Let $G=([n],E)$ be a simple undirected graph with adjacency matrix $A\in\{0,1\}^{n\times n}$, $A_{i,j}=1$ iff $\{i,j\}\in E$. For a pattern $H$ with $k$ vertices, the number of **non-induced copies** of $H$ in $G$ is
--   $$
--   f_H(G)=\frac{1}{|\mathrm{Aut}(H)|}\sum_{\phi:V(H)\hookrightarrow[n]}\ \prod_{\{u,v\}\in E(H)}A_{\phi(u),\phi(v)}=P(A).
--   $$
--   This is the quantity every algorithm of the mission estimates.
--
--   **Formalization Note** The input graph is a simple graph on $\mathrm{Fin}\,n$; $A$ is the $\{0,1\}$-valued function on unordered pairs.
-- source:
--   Chen–Peng, The Power of Interaction in Locally Edge-Private Subgraph Counting, arXiv:2611.05038 (held version, sha256 d18032b0…), §2.1, p.13–14 (PDF p.15–16)

import Mathlib
import Definitions.Def_LEDPCount_countPoly

namespace LEDPCount

/-- The adjacency matrix `A` of a graph `G = ([n], E)` (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, §2.1, p.13,
PDF p.15), as a function on unordered pairs: `A_e = 1` if `e ∈ E` and `0` otherwise.

**Formalization Note** The input graph is `G : SimpleGraph (Fin n)` (vertices 0-based); a
symmetric matrix is a function on `Sym2 (Fin n)` (the paper's upper-triangular convention). -/
noncomputable def adjMat {n : ℕ} (G : SimpleGraph (Fin n)) : Sym2 (Fin n) → ℝ := by
  classical
  exact fun e => if e ∈ G.edgeSet then 1 else 0

/-- `f_H(G)`, the number of non-induced copies of the pattern `H` in `G` (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…,
§2.1, p.14, PDF p.16): `f_H(G) = |Aut(H)|⁻¹ ∑_{ϕ : V(H) ↪ [n]} ∏_{{u,v} ∈ E(H)} A_{ϕ(u),ϕ(v)}`,
i.e. the counting polynomial (1) evaluated at the adjacency matrix, `P(A) = f_H(G)` (p.18). -/
noncomputable def subgraphCount {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj] {n : ℕ}
    (G : SimpleGraph (Fin n)) : ℝ :=
  countPoly H (adjMat G)

end LEDPCount


