-- Prove2me | Definitions.Def_SpecExtremalConj_specRad
-- name    : SpecExtremalConj_specRad
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:05:48.995986+00:00
-- url     : https://prove2.me/theorems/d1a04ea6-42d0-43b2-a1c9-36689b22b030
-- title:
--   Spectral radius $\lambda(G)$: largest adjacency eigenvalue
-- statement:
--   Let $G$ be a finite simple graph with adjacency matrix $A(G)=(a_{ij})$, where $a_{ij}=1$ if $ij\in E(G)$ and $a_{ij}=0$ otherwise. The **spectral radius** of $G$ is the largest eigenvalue of $A(G)$:
--
--   $$\lambda(G)=\max\{\mu : \mu \text{ is an eigenvalue of } A(G)\}.$$
--
--   Since $A(G)$ is real symmetric, all its eigenvalues are real, and $\lambda(G)$ is the largest of them.
--
--   This is the quantity maximized in the spectral Turán problem; every spectral statement of the mission is about it.
--
--   **Formalization Note** The definition takes the supremum of the eigenvalue list of the real symmetric matrix `G.adjMatrix ℝ` (`Matrix.IsHermitian.eigenvalues`). It is the largest eigenvalue, not the operator norm or Mathlib's `spectralRadius`; for adjacency matrices these agree by the Perron–Frobenius theorem, but that is not used in the definition. The vertex set may be any finite type (Lemma 2.7 uses complete multipartite graphs on a dependent-sum type). On an empty vertex set the value is $0$; no statement of the mission uses that case.
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, §2, p. 2 (unnumbered: "The spectral radius of G is the largest eigenvalue of A(G), denoted by λ(G)")

import Mathlib
open Finset SimpleGraph

namespace SpecExtremalConj

/-- **Spectral radius λ(G).** Wang, Kang, Xue, *On a conjecture of spectral extremal problems*, arXiv:2203.10831v1, §2, p. 2 (unnumbered):
"The adjacent matrix of G is A(G) = (a_ij) with a_ij = 1 if ij ∈ E(G), and a_ij = 0 otherwise.
The spectral radius of G is the largest eigenvalue of A(G), denoted by λ(G)."

`specRad G` is the largest eigenvalue of the real symmetric adjacency matrix `G.adjMatrix ℝ`,
taken as the supremum of the (real) eigenvalues listed by `Matrix.IsHermitian.eigenvalues`.

**Formalization Note.** This is the largest eigenvalue, as the paper defines it, not the
operator norm and not Mathlib's `spectralRadius` (which is `ℝ≥0∞`-valued and built from absolute
values); for adjacency matrices the two agree by Perron–Frobenius, but that is a theorem. The
vertex type is any finite type with decidable equality (Lemma 2.7 uses the Σ-type vertex set of
`completeMultipartiteGraph`). On an empty vertex type the supremum is `0`; no statement of the
mission uses that case. -/
noncomputable def specRad {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℝ :=
  ⨆ i, (G.isHermitian_adjMatrix ℝ).eigenvalues i

end SpecExtremalConj


