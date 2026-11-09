-- Prove2me | Definitions.Def_WeightedSpectralSketch_LowerBound_Leverage
-- name    : WeightedSpectralSketch_LowerBound_Leverage
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:56:15.511985+00:00
-- url     : https://prove2.me/theorems/d058dc6f-f3e4-42fb-aea5-29b3490c5a06
-- title:
--   Leverage score $\mathrm{lev}_v(U)$, minimum-norm coefficients and the pseudoinverse of a symmetric matrix
-- statement:
--   Let $(u_i)_{i\in I}$ be finitely many vectors in $\mathbb R^m$ and $v\in\mathbb R^m$. The **leverage score** of $v$ with respect to $(u_i)$ is (Eq. (1))
--
--   $$
--   \mathrm{lev}_v\big((u_i)_{i\in I}\big)=\min\Big\{\sum_{i\in I}c_i^2:\ v=\sum_{i\in I}c_iu_i\Big\}\in[0,\infty],
--   $$
--
--   with value $+\infty$ when $v$ is not in the span of the $u_i$. For a matrix $U$ we write $\mathrm{lev}_v(U)$ for the leverage with respect to its columns, and $U=[u_1\cdots u_m]$ is the matrix with columns $u_i$.
--
--   1. The **minimum-norm coefficient vector** of $v$ with respect to $(u_i)$ is the coefficient vector $c$ with $\sum_ic_iu_i=v$ of least $\sum_ic_i^2$ (it is unique when $v$ is representable); it is set to $0$ when $v$ is not representable.
--   2. For a real symmetric matrix $M=Q\,\mathrm{diag}(\lambda)\,Q^\top$ ($Q$ orthogonal), the **Moore–Penrose pseudoinverse** is $M^\dagger=Q\,\mathrm{diag}(\lambda^\dagger)\,Q^\top$, where $\lambda^\dagger=1/\lambda$ for $\lambda\ne0$ and $0^\dagger=0$.
--
--   Leverage scores measure how cheaply a vector is represented by other columns; the whole lower bound reduces to showing that the query column has small weighted leverage.
--
--   **Formalization Note.** The leverage is an infimum in $[0,\infty]$, so an infeasible representation gives $+\infty$ and not $0$. Squared norms are sums of squares of coordinates. The pseudoinverse uses Mathlib's spectral theorem for Hermitian matrices; Lean's convention $0^{-1}=0$ gives $\lambda^\dagger$.
-- source:
--   Chen, Chen and Yang, A Tight Superlinear Lower Bound on the Sketching Dimension of Weighted Spectral Sparsification, STOC 2027 submission #109 (2026), pinned preprint SHA-256 94f9d972f8c75c577e7195e080b6ed59e722471145d40426a2f0c92315be9f44, pp. 7–8, §3 (Moore–Penrose pseudoinverse), §3.1 Eq. (1) (leverage score), p. 15 Eq. (7) (minimum-norm representation), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/109.pdf

import Mathlib

open Matrix
open scoped ENNReal

namespace WeightedSpectralSketch.LowerBound

/-- The leverage score (1), p. 8, of a target vector `v` with respect to the vectors `(U i)_i`:
`lev_v(U) = min {∑ᵢ cᵢ² : v = ∑ᵢ cᵢ Uᵢ}`, valued in `[0, ∞]` and equal to `+∞` when `v` is not in
the span (the infimum over the empty set). -/
noncomputable def lev {ι m : Type*} [Fintype ι] (U : ι → m → ℝ) (v : m → ℝ) : ℝ≥0∞ :=
  ⨅ (c : ι → ℝ) (_ : ∑ i, c i • U i = v), ENNReal.ofReal (∑ i, c i ^ 2)

/-- The matrix `[U₁ ⋯ U_m]` whose columns are the vectors `U i`. -/
def colMat {ι m : Type*} (U : ι → m → ℝ) : Matrix m ι ℝ :=
  Matrix.of fun r i => U i r

/-- The minimum Euclidean-norm coefficient vector representing `v` by the vectors `U i`
(p. 15, (7)): the coefficient vector `c` with `∑ cᵢ Uᵢ = v` of least `∑ cᵢ²` (it is unique when it
exists); the zero vector when `v` is not representable. -/
noncomputable def minNormCoeff {ι m : Type*} [Fintype ι] (U : ι → m → ℝ) (v : m → ℝ) : ι → ℝ :=
  open Classical in
  if h : ∃ c : ι → ℝ, ∑ i, c i • U i = v ∧
      ∀ c' : ι → ℝ, ∑ i, c' i • U i = v → ∑ i, c i ^ 2 ≤ ∑ i, c' i ^ 2 then h.choose else 0

/-- The Moore–Penrose pseudoinverse `M†` of a real symmetric matrix (p. 7): with the spectral
decomposition `M = Q diag(λ) Qᵀ`, `M† = Q diag(λ†) Qᵀ`, where `λ† = 1/λ` for `λ ≠ 0` and `0† = 0`
(Lean's `0⁻¹ = 0`). -/
noncomputable def hermPinv {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ}
    (hM : M.IsHermitian) : Matrix n n ℝ :=
  (hM.eigenvectorUnitary : Matrix n n ℝ) * Matrix.diagonal (fun i => (hM.eigenvalues i)⁻¹) *
    star (hM.eigenvectorUnitary : Matrix n n ℝ)

end WeightedSpectralSketch.LowerBound


