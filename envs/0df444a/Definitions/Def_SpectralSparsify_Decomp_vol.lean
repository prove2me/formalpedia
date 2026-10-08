-- Prove2me | Definitions.Def_SpectralSparsify_Decomp_vol
-- name    : SpectralSparsify_Decomp_vol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T09:33:46.827118+00:00
-- url     : https://prove2.me/theorems/657c24dc-5887-4219-b292-1a37161fa533
-- title:
--   Volume Vol(S) = Σ_{i∈S} dᵢ of a vertex set, degrees taken in G (§4, p. 4)
-- statement:
--   Let $G=(V,E)$ be a finite simple graph and write $d_i$ for the degree of vertex $i$ in $G$. The **volume** of a vertex set $S\subseteq V$ is
--   $$\operatorname{Vol}(S)=\sum_{i\in S} d_i .$$
--   In particular $\operatorname{Vol}(V)=2m$ when $G$ has $m$ edges.
--
--   Throughout §7 of the paper, volumes of vertex sets of induced subgraphs $G(B)$ are still measured with the degrees $d_i$ of the original graph $G$, never with the degrees inside $G(B)$. Every conductance in this mission is built on this volume.
--
--   **Formalization Note** `vol G S` is the real number $\sum_{i\in S} d_i$ with `G.degree i` cast to $\mathbb R$, for `S : Finset V` and `G : SimpleGraph V` on a finite vertex type.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, p. 4, Section 4 (definition of Vol); p. 16, Section 7 (volumes measured in G)

import Mathlib

namespace SpectralSparsify.Decomp

/-- The volume of a vertex set (Spielman–Teng, *Spectral Sparsification of Graphs*,
arXiv:0808.4134v3, §4, p. 4): `Vol(S) = ∑_{i ∈ S} dᵢ`, where `dᵢ` is the degree of `i` in the
graph `G` itself. In §7 volumes are always measured with the degrees of the original graph `G`,
also for vertex sets of induced subgraphs. -/
noncomputable def vol {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : ℝ :=
  ∑ i ∈ S, (G.degree i : ℝ)

end SpectralSparsify.Decomp


