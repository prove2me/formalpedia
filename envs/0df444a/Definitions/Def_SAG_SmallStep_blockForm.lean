-- Prove2me | Definitions.Def_SAG_SmallStep_blockForm
-- name    : SAG_SmallStep_blockForm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T12:24:13.030676+00:00
-- url     : https://prove2.me/theorems/7eba2b01-f8e9-40cf-8754-fcda58a062f8
-- title:
--   Block matrices $P=(A\ b;\ b^\top\ c)$, $\mathrm{Diag}(\mathrm{diag}(\cdot))$, $S$ and $b-\frac{\alpha}{n}ec$ of Lemma 1
-- statement:
--   This file fixes the block-matrix vocabulary of Lemma 1 (pp. 13–16). Vectors of $\mathbb R^{np}$ are stacks $u=(u_1;\dots;u_n)$ of vectors $u_i\in\mathbb R^p$, and $e=(I;\dots;I)\in\mathbb R^{np\times p}$ stacks $n$ identity blocks.
--
--   1. A matrix $M\in\mathbb R^{np\times np}$ is given by its $p\times p$ blocks $M_{ij}$; its bilinear form is $u^\top M v=\sum_{i,j}\langle u_i, M_{ij}v_j\rangle$.
--   2. A matrix $B\in\mathbb R^{np\times p}$ is given by its blocks $B_i$; its bilinear form is $u^\top B w=\sum_i\langle u_i,B_iw\rangle$ for $w\in\mathbb R^p$.
--   3. For $A\in\mathbb R^{np\times np}$, $b\in\mathbb R^{np\times p}$, $c\in\mathbb R^{p\times p}$, the quadratic form of $P=\begin{pmatrix}A&b\\ b^\top&c\end{pmatrix}$ at $(u;w)$ is
--   $$
--   \begin{pmatrix}u\\ w\end{pmatrix}^{\!\top}\begin{pmatrix}A&b\\ b^\top&c\end{pmatrix}\begin{pmatrix}u\\ w\end{pmatrix}=u^\top Au+2u^\top bw+w^\top cw .
--   $$
--   4. $\mathrm{Diag}(\mathrm{diag}(M))$ is the block-diagonal matrix that keeps the diagonal blocks $M_{ii}$ of $M$ and zeroes the others.
--   5. For a step size $\alpha$,
--   $$
--   S=A-\frac{\alpha}{n}be^\top-\frac{\alpha}{n}eb^\top+\frac{\alpha^2}{n^2}ece^\top,
--   \qquad\text{blockwise}\quad S_{ij}=A_{ij}-\frac{\alpha}{n}b_i-\frac{\alpha}{n}b_j^\top+\frac{\alpha^2}{n^2}c,
--   $$
--   and $b-\frac{\alpha}{n}ec\in\mathbb R^{np\times p}$ has blocks $b_i-\frac{\alpha}{n}c$.
--
--   These are the objects in which Lemma 1 expresses the expected change of a quadratic Lyapunov function along one SAG step.
--
--   **Formalization Note** Blocks are continuous linear maps of `EuclideanSpace ℝ (Fin p)`; the transpose $b_j^\top$ is the adjoint `ContinuousLinearMap.adjoint (b j)`. Block indices are `Fin n`.
-- source:
--   Le Roux, Schmidt & Bach, A Stochastic Gradient Method with an Exponential Convergence Rate for Finite Training Sets, arXiv:1202.6258v4, p. 13 (e), p. 14 (diag, Diag), p. 16, Lemma 1 (P, S, b − (α/n)ec)

import Mathlib

namespace SAG.SmallStep

open scoped RealInnerProductSpace

/-- The bilinear form `uᵀ M v` of a block matrix `M ∈ ℝ^{np×np}` with `p × p` blocks `M i j`,
for stacked vectors `u = (u₁; …; uₙ)`, `v = (v₁; …; vₙ)`. -/
noncomputable def blockBil {p n : ℕ}
    (M : Fin n → Fin n → (EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)))
    (u v : Fin n → EuclideanSpace ℝ (Fin p)) : ℝ :=
  ∑ i, ∑ j, ⟪u i, M i j (v j)⟫

/-- The bilinear form `uᵀ B w` of a block column `B ∈ ℝ^{np×p}` with blocks `B i`. -/
noncomputable def colBil {p n : ℕ}
    (B : Fin n → (EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)))
    (u : Fin n → EuclideanSpace ℝ (Fin p)) (w : EuclideanSpace ℝ (Fin p)) : ℝ :=
  ∑ i, ⟪u i, B i w⟫

/-- The quadratic form `(u; w)ᵀ (A b; bᵀ c) (u; w) = uᵀAu + 2uᵀbw + wᵀcw` of the block matrix
`P = (A b; bᵀ c)` with `A ∈ ℝ^{np×np}`, `b ∈ ℝ^{np×p}`, `c ∈ ℝ^{p×p}` (p. 16, Lemma 1). -/
noncomputable def quadForm {p n : ℕ}
    (A : Fin n → Fin n → (EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)))
    (b : Fin n → (EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)))
    (c : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (u : Fin n → EuclideanSpace ℝ (Fin p)) (w : EuclideanSpace ℝ (Fin p)) : ℝ :=
  blockBil A u u + 2 * colBil b u w + ⟪w, c w⟫

/-- `Diag(diag(M))`: the block-diagonal matrix with the diagonal blocks of `M` (p. 14). -/
noncomputable def diagBlocks {p n : ℕ}
    (M : Fin n → Fin n → (EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p))) :
    Fin n → Fin n → (EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)) :=
  fun i j => if i = j then M i j else 0

/-- `S = A − (α/n) b eᵀ − (α/n) e bᵀ + (α²/n²) e c eᵀ` (p. 16, Lemma 1), where
`e = (I; …; I) ∈ ℝ^{np×p}`; blockwise `S i j = A i j − (α/n) b i − (α/n) (b j)ᵀ + (α²/n²) c`. -/
noncomputable def sMatrix {p n : ℕ} (α : ℝ)
    (A : Fin n → Fin n → (EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)))
    (b : Fin n → (EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)))
    (c : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)) :
    Fin n → Fin n → (EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)) :=
  fun i j => A i j - (α / (n : ℝ)) • b i - (α / (n : ℝ)) • ContinuousLinearMap.adjoint (b j)
    + (α ^ 2 / (n : ℝ) ^ 2) • c

/-- The block column `b − (α/n) e c ∈ ℝ^{np×p}` (p. 16, Lemma 1); blockwise `b i − (α/n) c`. -/
noncomputable def bMinusEc {p n : ℕ} (α : ℝ)
    (b : Fin n → (EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)))
    (c : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)) :
    Fin n → (EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)) :=
  fun i => b i - (α / (n : ℝ)) • c

end SAG.SmallStep


