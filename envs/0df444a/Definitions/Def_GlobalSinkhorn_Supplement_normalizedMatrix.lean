-- Prove2me | Definitions.Def_GlobalSinkhorn_Supplement_normalizedMatrix
-- name    : GlobalSinkhorn_Supplement_normalizedMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:55:47.71473+00:00
-- url     : https://prove2.me/theorems/45e215e9-952d-428c-9aad-6662ac4dd26b
-- title:
--   Symmetric margin normalization $Q_r^{-1/2}AQ_c^{-1/2}$
-- statement:
--   For an $n\times n$ matrix $A$ with row sums $A(i,[n])$ and column sums $A([n],j)$, let
--   $$
--   Q_r=\operatorname{diag}\big(A(1,[n]),\dots,A(n,[n])\big),\qquad Q_c=\operatorname{diag}\big(A([n],1),\dots,A([n],n)\big),
--   $$
--   and define the **normalized matrix**
--   $$
--   B=Q_r^{-1/2}\,A\,Q_c^{-1/2},\qquad B_{ij}=\frac{A_{ij}}{\sqrt{A(i,[n])\,A([n],j)}} .
--   $$
--   For a nonnegative $A$ with positive margins its largest singular value is $1$, and its second singular value $s_2(B)$ is the spectral parameter $\sigma$ of Lemma 4.4 and Theorem 4.5; applied to a dense matrix $D$ it is the matrix $E=\operatorname{diag}(r)^{-1/2}D\operatorname{diag}(c)^{-1/2}$ of Theorems 1.7 and 1.8. For a row-stochastic $A$ it equals $A\,Q_c^{-1/2}$.
--
--   **Formalization Note** $Q^{-1/2}$ is the diagonal matrix of $(\sqrt{s})^{-1}$; Lean's square root and inverse are total (value $0$ on a zero sum), but every statement using this matrix has positive row and column sums.
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), Lemma 4.4, Eqs. (71)–(72), p.27; Theorem 1.7 (E), p.8; Theorem 1.8 (1) (E_n), p.9

import Mathlib

open Matrix

namespace GlobalSinkhorn.Supplement

/-- The symmetrically normalized matrix `Q_r^{-1/2} A Q_c^{-1/2}`, where
`Q_r = diag(A(1,[n]), …, A(n,[n]))` and `Q_c = diag(A([n],1), …, A([n],n))` are the diagonal
matrices of row and column sums. He, Global Sinkhorn Convergence and Spectral Stability of Matrix
Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), Lemma 4.4, Eqs. (71)–(72),
p.27; the same matrix is `E = diag(r)^{-1/2} D diag(c)^{-1/2}` of Theorem 1.7 (p.8) and
`E_n = R_n^{-1/2} D_n C_n^{-1/2}` of Theorem 1.8 (p.9).

**Formalization Note.** `Q^{-1/2}` is the diagonal matrix with entries `(√s)⁻¹` for the row
(resp. column) sums `s`. Lean's `Real.sqrt` and inverse are total (value `0` on a zero sum);
every theorem using this matrix assumes, or derives from density, positive row and column sums,
so the junk value never occurs. -/
noncomputable def normalizedMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => (Real.sqrt (∑ j, A i j))⁻¹) * A *
    Matrix.diagonal (fun j => (Real.sqrt (∑ i, A i j))⁻¹)

end GlobalSinkhorn.Supplement


