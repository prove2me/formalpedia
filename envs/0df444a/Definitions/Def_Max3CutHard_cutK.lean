-- Prove2me | Definitions.Def_Max3CutHard_cutK
-- name    : Max3CutHard_cutK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:43:16.693245+00:00
-- url     : https://prove2.me/theorems/c4499da0-a7b1-4f02-a8d4-6652caa5e79a
-- title:
--   Cut weight $\mathrm{cut}_\chi(G)$ of a $k$-colouring of an $\mathbb N$-weighted graph
-- statement:
--   Let $G$ be a loopless multigraph on the vertex set $\{0,\dots,n-1\}$, in which an edge listed $m$ times has weight $m$, and let $\chi:\{0,\dots,n-1\}\to[k]=\{0,\dots,k-1\}$ be a colouring. The **cut weight** of $\chi$ is
--
--   $$\mathrm{cut}_\chi(G)=\sum_{\{u,v\}\in E}w_{uv}\,[\chi(u)\ne\chi(v)],$$
--
--   the total weight of the edges whose endpoints receive different colours.
--
--   This is the objective of Max-$k$-Cut on the integer-weighted graphs in which the mission's main theorem is stated.
--
--   **Formalization Note** The graph is the published `OptInapprox.MaxCut.WMaxCut`; the cut weight counts the listed edges with differently coloured endpoints.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, Cuts, p.4

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_UGC
open OptInapprox.MaxCut

namespace Max3CutHard

/-- **Cut weight of a `k`-colouring of an ℕ-weighted graph.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, Cuts, p.4:
"for a colouring `χ : V → [k]` let `cut_χ(G) = Σ_{u,v}∈E w_uv [χ(u) ≠ χ(v)]`".

**Formalization Note.** `G` is the published `OptInapprox.MaxCut.WMaxCut` (vertices `Fin G.n`, an
edge listed `m` times has weight `m`); colours `[k] = {0, …, k−1}` are `Fin k`. The cut weight is
the number of listed edges whose endpoints receive different colours. -/
def cutK (k : ℕ) (G : WMaxCut) (χ : Fin G.n → Fin k) : ℕ :=
  G.edges.countP fun e => χ e.1 ≠ χ e.2

end Max3CutHard


