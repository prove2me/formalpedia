-- Prove2me | Definitions.Def_PRUPermLayer_projMat
-- name    : PRUPermLayer_projMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:51.022251+00:00
-- url     : https://prove2.me/theorems/d8cf126c-82bd-4bb5-86cd-7e8662eb2edb
-- title:
--   Orthogonal projector $\Pi_K$ onto a subspace $K$
-- statement:
--   For a subspace $K$ of a finite-dimensional Hilbert space $\mathbb C^\iota$, $\Pi_K$ denotes the **orthogonal projector** onto $K$: the Hermitian idempotent operator with range $K$.
--
--   **Formalization Note** The matrix of Mathlib's orthogonal projection onto $K$. Sanity: the projector onto the whole space is $I$ and onto $\{0\}$ is $0$.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.1, p.8 (PDF p.10)

import Mathlib

namespace PRUPermLayer

/-- The orthogonal projector `Π_K` onto a subspace `K` of `ℂ^ι`, as a matrix (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.1, p.8
(PDF p.10): "We write Π, with a subscript, for the orthogonal projector onto the subspace named in
the subscript").

**Formalization Note** The matrix of Mathlib's orthogonal projection `K.starProjection`, through
`Matrix.toEuclideanLin`. Every subspace of a finite-dimensional space has one. Sanity:
`projMat ⊤ = 1` and `projMat ⊥ = 0`. -/
noncomputable def projMat {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Submodule ℂ (EuclideanSpace ℂ ι)) : Matrix ι ι ℂ :=
  Matrix.toEuclideanLin.symm (K.starProjection : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)

end PRUPermLayer


