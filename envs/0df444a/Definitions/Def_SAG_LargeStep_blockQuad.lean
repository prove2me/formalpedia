-- Prove2me | Definitions.Def_SAG_LargeStep_blockQuad
-- name    : SAG_LargeStep_blockQuad
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T12:24:15.178846+00:00
-- url     : https://prove2.me/theorems/4e6e2316-8e88-4838-b9dd-a0c4ec503cdd
-- title:
--   Block quadratic form (θ − θ*)ᵀ(A b; bᵀ c)(θ − θ*) and the matrix S of Lemma 1
-- statement:
--   Let $A\in\mathbb R^{np\times np}$, $b\in\mathbb R^{np\times p}$ and $c\in\mathbb R^{p\times p}$, written in $p\times p$ blocks $A_{ij}$, $b_i$ and $c$. For a block vector $u=(u_1,\dots,u_n)\in\mathbb R^{np}$ and $v\in\mathbb R^p$,
--   $$\begin{pmatrix}u\\v\end{pmatrix}^\top\begin{pmatrix}A&b\\ b^\top&c\end{pmatrix}\begin{pmatrix}u\\v\end{pmatrix}=\sum_{i,j}\langle u_i,A_{ij}u_j\rangle+2\sum_i\langle u_i,b_iv\rangle+\langle v,cv\rangle .$$
--   With $e=(I,\dots,I)^\top$ and a step size $\alpha$, the matrix of Lemma 1 is
--   $$S=A-\frac\alpha n be^\top-\frac\alpha n eb^\top+\frac{\alpha^2}{n^2}ece^\top,\qquad S_{ij}=A_{ij}-\frac\alpha n b_i-\frac\alpha n b_j^\top+\frac{\alpha^2}{n^2}c .$$
--
--   **Formalization Note** Blocks are continuous linear maps of `EuclideanSpace ℝ (Fin p)`; $b_j^\top$ is the adjoint `ContinuousLinearMap.adjoint (b j)`. `blockQuad A b c u v` is the quadratic form and `blockS A b c α i j` is $S_{ij}$.
-- source:
--   Le Roux, Schmidt & Bach, A Stochastic Gradient Method with an Exponential Convergence Rate for Finite Training Sets, arXiv:1202.6258v4, p. 16, Lemma 1

import Mathlib

namespace SAG.LargeStep

/-- The quadratic form `(u, v)ᵀ (A b; bᵀ c) (u, v)` on `ℝ^{(n+1)p}` (Lemma 1, p. 16), for a
block vector `u = (u₁, …, uₙ)` with `uᵢ ∈ ℝᵖ` and `v ∈ ℝᵖ`, where `A ∈ ℝ^{np×np}` is given by its
`p × p` blocks `A i j`, `b ∈ ℝ^{np×p}` by its blocks `b i`, and `c ∈ ℝ^{p×p}`:
`uᵀAu + 2 uᵀ b v + vᵀ c v = ∑ᵢⱼ ⟪uᵢ, Aᵢⱼ uⱼ⟫ + 2 ∑ᵢ ⟪uᵢ, bᵢ v⟫ + ⟪v, c v⟫`. -/
noncomputable def blockQuad {p n : ℕ}
    (A : Fin n → Fin n → EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (b : Fin n → EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (c : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (u : Fin n → EuclideanSpace ℝ (Fin p)) (v : EuclideanSpace ℝ (Fin p)) : ℝ :=
  ∑ i, ∑ j, inner ℝ (u i) (A i j (u j)) + 2 * ∑ i, inner ℝ (u i) (b i v) + inner ℝ v (c v)

/-- The `p × p` blocks of `S = A − (α/n) b eᵀ − (α/n) e bᵀ + (α²/n²) e c eᵀ` (Lemma 1, p. 16),
where `e = (I, …, I)ᵀ ∈ ℝ^{np×p}`: `Sᵢⱼ = Aᵢⱼ − (α/n) bᵢ − (α/n) bⱼᵀ + (α²/n²) c`. -/
noncomputable def blockS {p n : ℕ}
    (A : Fin n → Fin n → EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (b : Fin n → EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (c : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)) (α : ℝ) (i j : Fin n) :
    EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p) :=
  A i j - (α / (n : ℝ)) • b i - (α / (n : ℝ)) • ContinuousLinearMap.adjoint (b j)
    + (α ^ 2 / (n : ℝ) ^ 2) • c

end SAG.LargeStep


