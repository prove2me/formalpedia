-- Prove2me | Definitions.Def_DerandSq_lam
-- name    : DerandSq_lam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:53:20.793468+00:00
-- url     : https://prove2.me/theorems/6efe5d2c-b788-479a-8b98-240f545b2131
-- title:
--   Spectral expansion $\lambda(A) = \|A|_{\perp 1}\|$
-- statement:
--   For an $N \times N$ real matrix $A$ let $J = \mathbf 1 \mathbf 1^{\top}/N$ be the orthogonal projection onto the constant vectors and
--   $$
--   A|_{\perp 1} = (I - J)\, A\, (I - J).
--   $$
--   The **spectral expansion** of $A$ is the operator norm of $A|_{\perp 1}$ on Euclidean $\mathbb R^N$:
--   $$
--   \lambda(A) = \bigl\| (I - J) A (I - J) \bigr\|_{2 \to 2}.
--   $$
--   For the adjacency matrix $A$ of a regular graph (symmetric, constant row sums) this is the largest magnitude of a non-trivial eigenvalue of $A$, the quantity $\lambda(G)$ of an $(N, d, \lambda)$-graph (p.1): $A|_{\perp 1}$ has the eigenvalues of $A$ on $\mathbf 1^{\perp}$ and the eigenvalue $0$ on $\mathbf 1$.
--
--   **Formalization Note** The norm is that of `Matrix.toEuclideanCLM`. For instance $\lambda(I) = 1$ for $N \geq 2$ and $\lambda(\mathbf 1\mathbf 1^\top) = 0$.
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), p.1 (definition of $\lambda(G)$) and p.12 ($A|_{\perp 1}$)

import Mathlib

namespace DerandSq

/-- `λ(A)`, the spectral expansion of a graph with adjacency matrix `A` on `N` vertices
(Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), p.1: "the largest magnitude of any non-trivial eigenvalue of the adjacency matrix"):
the operator norm `‖A|_{⊥1}‖` of `A|_{⊥1} = (I − J) A (I − J)`, `J = 11ᵀ/N` (p.12), on
Euclidean `ℝ^N`.

**Formalization Note** For a symmetric `A` with constant row sums (the case of every graph in the
mission: the derandomized square of a matching-model graph is symmetric and `dk`-regular),
`A|_{⊥1}` has the eigenvalues of `A` on `1^⊥` and `0` on `1`, so its norm is the largest
non-trivial eigenvalue magnitude. -/
noncomputable def lam {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ)
    ((1 - (N : ℝ)⁻¹ • Matrix.of (fun _ _ : Fin N => (1 : ℝ))) * A *
      (1 - (N : ℝ)⁻¹ • Matrix.of (fun _ _ : Fin N => (1 : ℝ))))‖

end DerandSq


