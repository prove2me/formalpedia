-- Prove2me | Definitions.Def_WangKangXue_SpectralTuran_specRad
-- name    : WangKangXue_SpectralTuran_specRad
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T14:15:43.356659+00:00
-- url     : https://prove2.me/theorems/204e2ed9-b0e1-432b-9e3f-d239883d034c
-- title:
--   λ(G): the spectral radius (largest adjacency eigenvalue) of a finite simple graph
-- statement:
--   Let $G$ be a finite simple graph with vertex set $V$, $|V| = n$. Its **adjacency matrix** is the real symmetric $V\times V$ matrix $A(G) = (a_{uv})$ with $a_{uv} = 1$ if $uv \in E(G)$ and $a_{uv} = 0$ otherwise. Being real symmetric, $A(G)$ has $n$ real eigenvalues counted with multiplicity. The **spectral radius** of $G$ is the largest of them:
--   $$
--   \lambda(G) := \max\{\mu : \mu \text{ is an eigenvalue of } A(G)\}.
--   $$
--   For example $\lambda(K_2) = 1$, $\lambda(K_3) = 2$, and $\lambda$ of an edgeless graph is $0$.
--
--   This is the quantity maximised in spectral extremal problems: every result of the mission compares the spectral radii of $F$-free graphs.
--
--   **Formalization Note** The matrix is Mathlib's `G.adjMatrix ℝ`, and the value is `eigenvalues₀ ⟨0, _⟩` of its Hermitian structure; Mathlib lists these eigenvalues in decreasing order, so index $0$ is the largest eigenvalue, which is how the paper defines $\lambda(G)$ (no absolute values are taken). Adjacency is decided classically, so the value does not depend on a decidability instance. On an empty vertex type there is no eigenvalue and the value is $0$ by convention; every theorem of the mission concerns graphs with at least one vertex.
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, p. 2, Section 2 (definition of A(G) and λ(G))

import Mathlib

namespace WangKangXue.SpectralTuran

/-- `λ(G)`: the spectral radius of a finite simple graph `G` in the sense of Wang–Kang–Xue
(arXiv:2203.10831v1, p. 2), i.e. the **largest eigenvalue** of the real adjacency matrix
`A(G)` (`G.adjMatrix ℝ`, entry `1` on edges and `0` elsewhere).
Mathlib's `Matrix.IsHermitian.eigenvalues₀` lists the eigenvalues (with multiplicity) in
decreasing order (`eigenvalues₀_antitone`), so index `0` is the largest one.
Decidability of adjacency is taken classically, so the value does not depend on an instance.
On the empty vertex type there is no eigenvalue and the value is `0` by convention. -/
noncomputable def specRad {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ℝ := by
  classical
  exact
    if h : 0 < Fintype.card V then
      (G.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨0, h⟩
    else 0

end WangKangXue.SpectralTuran


