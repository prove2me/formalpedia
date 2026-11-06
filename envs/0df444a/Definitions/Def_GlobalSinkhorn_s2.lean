-- Prove2me | Definitions.Def_GlobalSinkhorn_s2
-- name    : GlobalSinkhorn_s2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T04:21:29.20863+00:00
-- url     : https://prove2.me/theorems/0e807e3d-21ae-4e74-9359-f9a03e2068b9
-- title:
--   The second singular value $s_2(B)$, counted with multiplicity
-- statement:
--   For a real $n\times n$ matrix $B$, $s_2(B)$ is its **second-largest singular value**, with singular values counted with multiplicity: if $s_1(B)\ge s_2(B)\ge\dots\ge s_n(B)\ge0$ are the square roots of the eigenvalues of $B^\top B$, listed with multiplicity, then $s_2(B)$ is the second entry of this list. For example, the $2\times2$ identity has $s_2=1$, and the all-$\tfrac12$ matrix of size 2 (rank one) has $s_2=0$.
--
--   For a doubly stochastic $B$ one has $s_1(B)=1$, and the endpoint spectral gap $g=1-s_2(B)^2$ governs the convergence rate of Sinkhorn–Knopp in Theorem 1.1.
--
--   **Formalization Note** $s_2(B)$ is `(Matrix.toEuclideanLin B).singularValues 1`: Mathlib's singular values of the linear map on $\mathbb R^n$ with the standard inner product, 0-indexed, nonincreasing, with multiplicity. For $n\le1$ the value is $0$.
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), Section 1, p.3

import Mathlib

open Matrix

namespace GlobalSinkhorn

/-- `s₂(B)`, the second-largest singular value of `B`, counted with multiplicity.
He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), p.3.

**Formalization Note.** `LinearMap.singularValues` is 0-indexed, nonincreasing and repeats each
value with its multiplicity, so index `1` is the second singular value. `Matrix.toEuclideanLin`
acts on `EuclideanSpace ℝ (Fin n)`, so the inner product is the standard one. For `n ≤ 1` the
value is `0`; every statement of this mission that uses it in a nondegenerate way has `2 ≤ n`
or remains the paper's statement at `n = 1`. -/
noncomputable def s2 {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (Matrix.toEuclideanLin B).singularValues 1

end GlobalSinkhorn


