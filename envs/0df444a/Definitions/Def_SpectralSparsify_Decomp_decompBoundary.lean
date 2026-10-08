-- Prove2me | Definitions.Def_SpectralSparsify_Decomp_decompBoundary
-- name    : SpectralSparsify_Decomp_decompBoundary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T09:33:34.342485+00:00
-- url     : https://prove2.me/theorems/ad7f36f6-5963-4e6d-b22b-90bb6b2a4ff5
-- title:
--   Boundary ∂(A₁, …, A_k) = E ∩ ⋃_{i≠j} (Aᵢ × Aⱼ) of a decomposition (§7.1, p. 17)
-- statement:
--   Let $G=(V,E)$ be a finite simple graph. A **decomposition** of $G$ is a partition of $V$ into nonempty sets $(A_1,\dots,A_k)$, for some $k$. Its **boundary** is the set of edges between different parts:
--   $$\partial(A_1,\dots,A_k)=E\cap\bigcup_{i\neq j}(A_i\times A_j).$$
--
--   The size $|\partial(A_1,\dots,A_k)|$ is the number of edges a decomposition cuts; Theorem 7.1 bounds it by $|E|/2$.
--
--   **Formalization Note** A decomposition is a `Finpartition` of `Finset.univ`, whose parts are nonempty, pairwise disjoint and cover $V$. `decompBoundary G P` is the finset of edges $\{u,v\}$ of $G$ (as elements of `Sym2 V`) with $u$ and $v$ in two different parts.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, p. 17, Section 7.1 (decomposition and its boundary)

import Mathlib

namespace SpectralSparsify.Decomp

/-- The boundary `∂(A₁, …, A_k) = E ∩ ⋃_{i ≠ j} (Aᵢ × Aⱼ)` of a decomposition
(arXiv:0808.4134v3, §7.1, p. 17): the set of edges of `G` whose two ends lie in different parts.
A decomposition of `G` is a partition of `V` into parts `A₁, …, A_k`, represented as a
`Finpartition` of `Finset.univ`. -/
def decompBoundary {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Finpartition (Finset.univ : Finset V)) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∃ A ∈ P.parts, ∃ A' ∈ P.parts, A ≠ A' ∧
    ∃ u ∈ A, ∃ v ∈ A', e = s(u, v))

end SpectralSparsify.Decomp


