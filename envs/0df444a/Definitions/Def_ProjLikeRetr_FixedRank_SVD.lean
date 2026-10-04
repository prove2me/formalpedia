-- Prove2me | Definitions.Def_ProjLikeRetr_FixedRank_SVD
-- name    : ProjLikeRetr_FixedRank_SVD
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T02:42:27.512358+00:00
-- url     : https://prove2.me/theorems/44a6ea42-e897-44b7-917a-bb3757da7b47
-- title:
--   (3.5)–(3.7), pp. 8–9 — singular values σ_i(X), a singular value decomposition X = UΣVᵀ, and its truncation Σ_{i≤r} σ_i u_i v_iᵀ
-- statement:
--   Let $X\in\mathbb R^{n\times m}$. This file fixes three objects of §3.2.
--
--   1. **Singular values.** For $i\ge1$, $\sigma_i(X)$ is the $i$-th largest singular value of $X$ (the square roots of the eigenvalues of $X^\top X$, in nonincreasing order, with multiplicity), so that
--   $$\sigma_1(X)\ge\sigma_2(X)\ge\cdots\ge\sigma_{\min\{n,m\}}(X)\ge0,$$
--   and $\sigma_i(X)=0$ for $i>\min\{n,m\}$.
--
--   2. **Singular value decomposition** (3.5). A triple $(U,\Sigma,V)$ is a singular value decomposition of $X$ if
--   $$X=U\Sigma V^\top,$$
--   where $U\in\mathbb R^{n\times n}$ and $V\in\mathbb R^{m\times m}$ are orthogonal, the only nonzero entries of the rectangular matrix $\Sigma\in\mathbb R^{n\times m}$ are on its diagonal, and the diagonal entries $\Sigma_{11},\Sigma_{22},\dots$ are nonnegative and nonincreasing.
--
--   3. **Truncation** (3.7). Writing $U=[u_1,\dots,u_n]$ and $V=[v_1,\dots,v_m]$, the truncated decomposition of rank $r$ keeps the first $r$ diagonal entries of $\Sigma$:
--   $$\hat X=U\,\Sigma^{(r)}\,V^\top=\sum_{i=1}^{\min\{r,n,m\}}\Sigma_{ii}\,u_iv_i^\top,\qquad \Sigma^{(r)}_{ij}=\begin{cases}\Sigma_{ii}&i=j\le r,\\0&\text{otherwise.}\end{cases}$$
--
--   The diagonal entries of $\Sigma$ in any singular value decomposition of $X$ are exactly the singular values $\sigma_i(X)$, so $\hat X=\sum_{i=1}^r\sigma_i(X)u_iv_i^\top$ is the matrix of (3.7) and of Proposition 3.3; that identification is a fact to be proved, not part of the definitions.
--
--   **Formalization Note** `sv X i` is Mathlib's `LinearMap.singularValues` of `Matrix.toEuclideanLin X` (the map $\mathbb R^m\to\mathbb R^n$ with Euclidean inner products), which is 0-based; `sv X i` evaluates it at `i - 1`, so `sv` is 1-based like the page. Only `i ≥ 1` is meaningful (`sv X 0` equals $\sigma_1(X)$ by natural-number subtraction); every statement of the mission uses indices $\ge1$. `IsSVD X U S V` is the predicate of (3.5), with `S` playing $\Sigma$ and "diagonal" meaning row index = column index as natural numbers. `truncSVD r U S V` is $U\Sigma^{(r)}V^\top$, with 0-based diagonal positions $<r$.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, pp. 8–9, §3.2, display (3.5) and the nonincreasing order of singular values; p. 9, display (3.7)

import Mathlib

namespace ProjLikeRetr.FixedRank

open scoped Matrix

/-- §3.2, p. 9: the `i`-th singular value `σ_i(X)` of a real `n × m` matrix `X`, **1-based** as on
the page: `σ_1(X) ≥ σ_2(X) ≥ ⋯ ≥ σ_{min{n,m}}(X) ≥ 0`, and `σ_i(X) = 0` for `i > min{n,m}`.
It is Mathlib's (0-based) `LinearMap.singularValues` of `X` acting `ℝ^m → ℝ^n` with the Euclidean
inner products, evaluated at `i - 1`. Only indices `i ≥ 1` are meaningful (at `i = 0` the natural
subtraction makes `sv X 0 = σ_1(X)`); every statement of the mission uses `i ≥ 1`. -/
noncomputable def sv {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℝ) (i : ℕ) : ℝ :=
  (Matrix.toEuclideanLin X).singularValues (i - 1)

/-- (3.5), pp. 8–9: `X = U Σ Vᵀ` is a singular value decomposition of `X ∈ ℝ^{n×m}`:
`U ∈ ℝ^{n×n}` and `V ∈ ℝ^{m×m}` are orthogonal, the only nonzero entries of the rectangular
`Σ ∈ ℝ^{n×m}` (here `S`) are on its diagonal (the entries `S i j` with `i = j` as natural numbers),
these diagonal entries are nonnegative and written in nonincreasing order of the index. -/
def IsSVD {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℝ) (U : Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin m) ℝ) (V : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  U ∈ Matrix.orthogonalGroup (Fin n) ℝ ∧ V ∈ Matrix.orthogonalGroup (Fin m) ℝ ∧
    (∀ i j, i.val ≠ j.val → S i j = 0) ∧
    (∀ i j, i.val = j.val → 0 ≤ S i j) ∧
    (∀ i j i' j', i.val = j.val → i'.val = j'.val → i.val ≤ i'.val → S i' j' ≤ S i j) ∧
    X = U * S * Vᵀ

/-- (3.7), p. 9: the truncated singular value decomposition `Σ_{i=1}^r σ_i(X) u_i v_iᵀ` built from an
SVD `X = U S Vᵀ`: keep the first `r` diagonal entries of `S` (0-based diagonal positions `< r`),
replace every other entry by `0`, and multiply back by `U` and `Vᵀ`. Here `u_i`, `v_i` are the
columns of `U`, `V`. -/
def truncSVD {n m : ℕ} (r : ℕ) (U : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin m) ℝ)
    (V : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin n) (Fin m) ℝ :=
  U * Matrix.of (fun i j => if i.val = j.val ∧ i.val < r then S i j else 0) * Vᵀ

end ProjLikeRetr.FixedRank


