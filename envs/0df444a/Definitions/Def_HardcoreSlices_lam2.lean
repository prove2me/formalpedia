-- Prove2me | Definitions.Def_HardcoreSlices_lam2
-- name    : HardcoreSlices_lam2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:35:58.128592+00:00
-- url     : https://prove2.me/theorems/b826cc95-d4a2-4719-866d-49d1984036dc
-- title:
--   The second adjacency eigenvalue $\lambda_2(A_G)$
-- statement:
--   $\lambda_2(A_G)$ is the second largest eigenvalue of the adjacency matrix of $G$, counted with multiplicity. On a random regular bipartite graph it is the quantity bounded by Friedman's theorem, and it drives the spectral bounds of both slices.
--
--   **Formalization Note** The eigenvalues are the sorted list `eigenvalues₀` of the Hermitian adjacency matrix. On a vertex type with fewer than two elements the value is $0$, which never occurs in the statements.
-- source:
--   Kocurek, Oveis Gharan, Tjowasi, Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold, arXiv:2604.21847 (version held, sha256 363c225d…), Theorem 2.4, p.10

import Mathlib

open Classical

namespace HardcoreSlices

/-- The adjacency matrix of a simple graph is Hermitian. -/
theorem adjMatrix_isHermitian {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W) :
    (G.adjMatrix ℝ).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  exact G.isSymm_adjMatrix

/-- **`λ2(AG)`**, the second largest eigenvalue of the adjacency matrix counted with multiplicity
(Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), Theorem 2.4, p.10).

**Formalization Note.** `eigenvalues₀` is the eigenvalue list sorted in decreasing order. On a vertex type with
fewer than two elements there is no second eigenvalue and the value is `0`; the statements using `lam2` concern
graphs with at least two vertices. -/
noncomputable def lam2 {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W) : ℝ :=
  if h : 2 ≤ Fintype.card W then
    (adjMatrix_isHermitian G).eigenvalues₀ ⟨1, h⟩
  else 0

end HardcoreSlices


