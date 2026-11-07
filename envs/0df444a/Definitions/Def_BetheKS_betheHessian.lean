-- Prove2me | Definitions.Def_BetheKS_betheHessian
-- name    : BetheKS_betheHessian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:34:13.717695+00:00
-- url     : https://prove2.me/theorems/4ca08697-8591-4f8c-84b1-9698e6cfb9e9
-- title:
--   The Bethe Hessian $H(t,G)=(t^2-1)I+D-tA$ and increasingly ordered eigenvalues and eigenbases
-- statement:
--   For a graph $G$ on $[n]$ with adjacency matrix $A$ and degree matrix $D$, the **Bethe Hessian** is
--   $$
--   H(t,G):=(t^2-1)I+D-tA .
--   $$
--   It is real symmetric. Its eigenvalues are ordered **increasingly**, "from most negative to most positive": $\lambda_1(H)\le\lambda_2(H)\le\dots\le\lambda_n(H)$. An *increasing orthonormal eigenbasis* of $H$ is an orthonormal basis $v_1,\dots,v_n$ of $\mathbb R^n$ (Euclidean norm) with $Hv_i=\lambda_iv_i$ and $\lambda_1\le\dots\le\lambda_n$; the paper uses $H(\sqrt d,G)$ and $H(-\sqrt d,G)$.
--
--   **Formalization Note** $\lambda_j$ is read off the sorted real roots of the characteristic polynomial, 0-based. When eigenvalues repeat, the eigenbasis is not unique; every statement of the mission quantifies over all such bases.
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), §1, p.1; Theorem 2.2, p.5

import Mathlib

set_option autoImplicit false

namespace BetheKS

/-- **The Bethe Hessian** `H(t, G) := (t² − 1) I + D − t A` — Dong, McKenzie, arXiv:2610.41802
(held version, sha256 4da41e16…), §1, p.1, of a graph `G` on `[n]` with degree matrix `D` and
adjacency matrix `A`. It is a real symmetric matrix.

**Formalization Note.** Adjacency is decided classically. -/
noncomputable def bh (t : ℝ) {n : ℕ} (G : SimpleGraph (Fin n)) : Matrix (Fin n) (Fin n) ℝ := by
  classical
  exact (t ^ 2 - 1) • (1 : Matrix (Fin n) (Fin n) ℝ) + G.degMatrix ℝ - t • G.adjMatrix ℝ

/-- The `j`-th eigenvalue (`j = 0, 1, …`) of a real square matrix in **increasing** order, "from
most negative to most positive" (Theorem 2.2, p.5): the `j`-th entry of the sorted multiset of real
roots of the characteristic polynomial.

**Formalization Note.** Indices are 0-based: `eigInc H 0` is the paper's `λ₁`. For a real
symmetric matrix the characteristic polynomial splits over `ℝ`, so these are all `n` eigenvalues
with multiplicity. Out-of-range indices return `0`; the paper uses only indices `< r₊ ≤ n`. -/
noncomputable def eigInc {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (j : ℕ) : ℝ :=
  ((H.charpoly.roots).sort (· ≤ ·)).getD j 0

/-- An orthonormal eigenbasis of a real symmetric matrix `H`, listed with **increasing**
eigenvalues (Theorem 2.2, p.5: "Order the eigenvalues of each Bethe Hessian increasingly").
`vec 0` is an eigenvector of the most negative eigenvalue.

**Formalization Note.** Vectors live in `EuclideanSpace ℝ (Fin n)` (the `ℓ²` norm of the paper).
When eigenvalues repeat the basis is not unique; every statement of the mission that uses it
quantifies over all such bases. -/
structure IncEigenbasis {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) where
  /-- the eigenvectors -/
  vec : Fin n → EuclideanSpace ℝ (Fin n)
  /-- their eigenvalues -/
  val : Fin n → ℝ
  orthonormal : Orthonormal ℝ vec
  eigen : ∀ i, Matrix.toEuclideanLin H (vec i) = val i • vec i
  mono : Monotone val

end BetheKS


