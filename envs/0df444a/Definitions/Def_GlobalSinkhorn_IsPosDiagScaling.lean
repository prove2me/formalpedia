-- Prove2me | Definitions.Def_GlobalSinkhorn_IsPosDiagScaling
-- name    : GlobalSinkhorn_IsPosDiagScaling
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T04:21:26.489721+00:00
-- url     : https://prove2.me/theorems/b8f56b28-2b07-4bce-85bd-06cd0464d554
-- title:
--   Positive diagonal scaling $B=XAY$
-- statement:
--   Let $A,B$ be real $n\times n$ matrices and $x,y\in\mathbb R^n$. The matrix $B$ is the **positive diagonal scaling** of $A$ by $(x,y)$ if $x_i>0$ and $y_j>0$ for all $i,j$ and
--   $$
--   B=XAY,\qquad X=\operatorname{diag}(x_1,\dots,x_n),\quad Y=\operatorname{diag}(y_1,\dots,y_n),
--   $$
--   that is, $B_{ij}=x_iA_{ij}y_j$ for all $i,j$. "$B$ is a positive diagonal scaling of $A$" means that some such $(x,y)$ exists.
--
--   **Formalization Note** Indices are `Fin n` (0-based). The paper's standing normalization $\min_i x_i=\min_j y_j$ (p.13) is not part of this predicate: rescaling $(x,y)\mapsto(cx,y/c)$ changes neither $B$ nor any product $x_iy_j$.
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), Theorem 3.1, p.15; Theorem 1.1, p.5

import Mathlib

open Matrix

namespace GlobalSinkhorn

/-- `B = X A Y` with `X = diag x`, `Y = diag y` positive diagonal: `B` is a positive diagonal
scaling of `A`. He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), Theorem 3.1, p.15 and Theorem 1.1, p.5.

**Formalization Note.** Indices `[n]` are `Fin n` (0-based). The convention `min x = min y` of
p.13 is not part of this predicate: it changes neither `B` nor any product `x i * y j`. -/
def IsPosDiagScaling {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) : Prop :=
  (∀ i, 0 < x i) ∧ (∀ j, 0 < y j) ∧ B = Matrix.diagonal x * A * Matrix.diagonal y

end GlobalSinkhorn


