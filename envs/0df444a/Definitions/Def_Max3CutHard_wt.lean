-- Prove2me | Definitions.Def_Max3CutHard_wt
-- name    : Max3CutHard_wt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:43:12.577082+00:00
-- url     : https://prove2.me/theorems/d9a2334a-7d14-42d4-ae57-e78dce1a43db
-- title:
--   Total edge weight $w(G)$ of an $\mathbb N$-weighted graph
-- statement:
--   For a loopless multigraph $G$ in which an edge listed $m$ times has weight $m$, the **total edge weight** is
--
--   $$w(G)=\sum_{\{u,v\}\in E}w_{uv},$$
--
--   the number of listed edges.
--
--   It is the normaliser of the cut fractions in Theorem 1.1.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, Cuts, p.4

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_UGC
open OptInapprox.MaxCut

namespace Max3CutHard

/-- **Total edge weight `w(G)` of an ℕ-weighted graph.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, Cuts, p.4:
"`w(G) = Σ_{u,v}∈E w_uv`".

**Formalization Note.** For the published `WMaxCut` (an edge listed `m` times has weight `m`) the
total weight is the length of the edge list. -/
def wt (G : WMaxCut) : ℕ := G.edges.length

end Max3CutHard


