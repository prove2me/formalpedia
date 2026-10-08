-- Prove2me | Definitions.Def_ProjLikeRetr_Stiefel_SVD
-- name    : ProjLikeRetr_Stiefel_SVD
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T15:11:38.936788+00:00
-- url     : https://prove2.me/theorems/f0bb3e0c-8da3-4a3b-aada-6bd575a213df
-- title:
--   Proposition 3.4, p. 10 — the orthonormal frame Σ_{i=1}^m u_i v_iᵀ = U E Vᵀ of a singular value decomposition (3.5)
-- statement:
--   Let $m\le n$ and let $X=U\Sigma V^\top$ be a singular value decomposition (3.5) of $X\in\mathbb R^{n\times m}$, with $U=[u_1,\dots,u_n]\in\mathbb R^{n\times n}$ and $V=[v_1,\dots,v_m]\in\mathbb R^{m\times m}$ orthogonal. This file defines the matrix of Proposition 3.4,
--
--   $$\sum_{i=1}^{m}u_iv_i^\top=U\,E\,V^\top,$$
--
--   where $E\in\mathbb R^{n\times m}$ is the rectangular identity ($E_{ij}=1$ if $i=j$ and $0$ otherwise; $E=\begin{bmatrix}I_m\\0\end{bmatrix}$ when $m\le n$). The proof of Proposition 3.4 writes this matrix $UV^\top$, keeping only the first $m$ columns of $U$.
--
--   **Formalization Note** `rectId n m` is $E$ and `frameOfSVD U V` is $UEV^\top$; for general $n,m$ it is $\sum_{i=1}^{\min\{n,m\}}u_iv_i^\top$. The singular values $\sigma_i(X)$ (`ProjLikeRetr.FixedRank.sv`, 1-based) and the singular value decomposition predicate (`ProjLikeRetr.FixedRank.IsSVD`) come from the shared module `Definitions.Def_ProjLikeRetr_FixedRank_SVD`, which this file imports.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 10, §3.3, Proposition 3.4 (Σ_{i=1}^m u_i v_iᵀ) and its proof (Y = UVᵀ); SVD notation (3.5), pp. 8–9

import Mathlib
import Definitions.Def_ProjLikeRetr_FixedRank_SVD

open scoped Matrix

namespace ProjLikeRetr.Stiefel

/-- The rectangular `n × m` "identity" `E` with entries `E i j = 1` if `i = j` (as natural numbers)
and `0` otherwise; for `m ≤ n` it is `[I_m; 0]`. -/
def rectId (n m : ℕ) : Matrix (Fin n) (Fin m) ℝ :=
  Matrix.of (fun i j => if i.val = j.val then 1 else 0)

/-- Proposition 3.4, p. 10: the matrix `Σ_{i=1}^m u_i v_iᵀ` built from the orthogonal factors of a
singular value decomposition `X = U Σ Vᵀ` (`u_i`, `v_i` the columns of `U`, `V`). It equals
`U E Vᵀ` with `E = rectId n m`; this is the matrix the proof writes `U Vᵀ` (keeping only the first
`m` columns of `U`). -/
def frameOfSVD {n m : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (V : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin n) (Fin m) ℝ :=
  U * rectId n m * Vᵀ

end ProjLikeRetr.Stiefel


