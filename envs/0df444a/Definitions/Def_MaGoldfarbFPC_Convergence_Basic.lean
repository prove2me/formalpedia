-- Prove2me | Definitions.Def_MaGoldfarbFPC_Convergence_Basic
-- name    : MaGoldfarbFPC_Convergence_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:40:25.538119+00:00
-- url     : https://prove2.me/theorems/933445c8-3743-42e6-ae78-bdbf06a71f71
-- title:
--   Problem (1.8), its optimal set, g and h, the step-size range τ ∈ (0, 2/λmax(AᵀA)) and the fixed point iterations (2.1)
-- statement:
--   This file fixes the objects of Ma, Goldfarb and Chen's analysis of the fixed point iterations for nuclear norm regularized least squares.
--
--   Let $m, n, p$ be natural numbers. A linear map $\mathcal A:\mathbb R^{m\times n}\to\mathbb R^p$ is given by $p$ matrices $A_0,\dots,A_{p-1}\in\mathbb R^{m\times n}$ through $\mathcal A(X)_i=\langle A_i,X\rangle=\sum_{j,k}(A_i)_{jk}X_{jk}$; its adjoint is $\mathcal A^*(y)=\sum_i y_iA_i$, and $\|\mathcal A\|_2=\sup\{\|\mathcal A(X)\|_2:\|X\|_F=1\}$ is its spectral norm. Let $b\in\mathbb R^p$ and $\mu,\tau\in\mathbb R$.
--
--   1. **Problem (1.8).** The objective is
--   $$F_\mu(X)=\mu\|X\|_*+\tfrac12\|\mathcal A(X)-b\|_2^2,$$
--   where $\|X\|_*$ is the nuclear norm (sum of the singular values) and $\|v\|_2^2=\sum_i v_i^2$. A matrix $X^*$ is an **optimal solution** of (1.8), written $X^*\in\mathcal X^*$, if $F_\mu(X^*)\le F_\mu(X)$ for every $X\in\mathbb R^{m\times n}$.
--   2. **The gradient map** $g(X)=\mathcal A^*(\mathcal A(X)-b)$, the gradient of $\tfrac12\|\mathcal A(X)-b\|_2^2$, and the **gradient step** $h(X)=X-\tau g(X)$, i.e. $h=I-\tau g$.
--   3. **The step-size range.** $\tau$ lies in $(0,2/\lambda_{\max}(A^\top A))$, where $A\in\mathbb R^{p\times mn}$ is the matrix of $\mathcal A$ (so $\mathcal A X=A\,\mathrm{vec}(X)$ and $\lambda_{\max}(A^\top A)=\|\mathcal A\|_2^2$). It is written
--   $$0<\tau\quad\text{and}\quad \tau\,\|\mathcal A\|_2^2<2 .$$
--   4. **The fixed point iterations (2.1).** A sequence $(X^k)_{k\ge0}$ in $\mathbb R^{m\times n}$, with arbitrary $X^0$, is a run of the iterations if for every $k$
--   $$Y^k=X^k-\tau g(X^k),\qquad X^{k+1}=S_{\tau\mu}(Y^k),$$
--   where $S_\nu$ is the matrix shrinkage operator: for a singular value decomposition $Y=U\,\mathrm{Diag}(\sigma)V^\top$, $S_\nu(Y)=U\,\mathrm{Diag}(\bar\sigma)V^\top$ with $\bar\sigma_i=\max(\sigma_i-\nu,0)$.
--
--   These are the objects in which Corollary 1, Lemmas 2–3 and Theorem 4 of the paper are stated.
--
--   **Formalization Note** Matrices are `Mat m n = Matrix (Fin m) (Fin n) ℝ`; the Frobenius norm `frobNorm`, the nuclear norm `nuclearNorm` (sum of Mathlib's singular values), `applyA`, `adjA`, `opNormA` and the shrinkage relation `IsShrink` are reused from the published Cai–Candès–Shen definitions. Every linear map $\mathbb R^{m\times n}\to\mathbb R^p$ has the form `applyA Aop` ($A_i$ is row $i$ of $A$, reshaped). `IsShrink ν Y X` says that $X=U\,\mathrm{Diag}(\max(\sigma_i-\nu,0))V^\top$ for *some* reduced SVD of $Y$ (orthonormal columns, $\sigma_i>0$); the paper's Definition 4 allows zero singular values, which shrink to zero and change nothing. The shrinkage is a relation rather than a function, so the run is a predicate on the whole sequence. The step-size range is stated without division: Lean's $2/0=0$ would otherwise empty the range when $\mathcal A=0$, whereas on paper the range is then $(0,\infty)$. The paper's standing hypotheses $\mu>0$ and $\nu=\tau\mu$ appear in each theorem, not here.
-- source:
--   Ma, Goldfarb and Chen, Fixed point and Bregman iterative methods for matrix rank minimization, arXiv:0905.1643v2, p. 4 (1.8); p. 6 Notation (g); p. 7 (2.1); p. 8 Definitions 3–4; p. 9 Corollary 1 (h); p. 11 Lemma 2 (τ ∈ (0, 2/λmax(AᵀA)))

import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Basic
import Definitions.Def_CaiCandesShen_Convergence_Problems
import Definitions.Def_CaiCandesShen_Convergence_Shrink

namespace MaGoldfarbFPC.Convergence

open CaiCandesShen.Convergence

/-- `‖v‖₂² = ∑ᵢ vᵢ²` for `v ∈ ℝ^p`. -/
def sqNorm2 {p : ℕ} (v : Fin p → ℝ) : ℝ := ∑ i, v i ^ 2

/-- The objective of problem (1.8), p. 4: `μ‖X‖_* + ½‖𝒜(X) − b‖₂²`, where the linear map
`𝒜 : ℝ^{m×n} → ℝ^p` is given by the matrices `Aop i` through `𝒜(X)ᵢ = ⟨Aop i, X⟩`
(the published `applyA`). -/
noncomputable def obj {m n p : ℕ} (μ : ℝ) (Aop : Fin p → Mat m n) (b : Fin p → ℝ)
    (X : Mat m n) : ℝ :=
  μ * nuclearNorm X + 1 / 2 * sqNorm2 (applyA Aop X - b)

/-- `X` is an optimal solution of problem (1.8), i.e. `X ∈ 𝒳*` (Theorem 4, p. 12): it
minimizes the objective over all of `ℝ^{m×n}`. -/
def IsOptimal {m n p : ℕ} (μ : ℝ) (Aop : Fin p → Mat m n) (b : Fin p → ℝ) (X : Mat m n) :
    Prop :=
  ∀ X' : Mat m n, obj μ Aop b X ≤ obj μ Aop b X'

/-- `g(X) = 𝒜*(𝒜(X) − b)`, the gradient of `½‖𝒜(X) − b‖₂²` (Notation, p. 6). -/
def g {m n p : ℕ} (Aop : Fin p → Mat m n) (b : Fin p → ℝ) (X : Mat m n) : Mat m n :=
  adjA Aop (applyA Aop X - b)

/-- `h(X) = X − τ g(X)`, i.e. `h(·) = I(·) − τg(·)` (Corollary 1, p. 9). -/
def h {m n p : ℕ} (τ : ℝ) (Aop : Fin p → Mat m n) (b : Fin p → ℝ) (X : Mat m n) :
    Mat m n :=
  X - τ • g Aop b X

/-- The step-size range `τ ∈ (0, 2/λ_max(AᵀA))` of Lemmas 2–3 and Theorem 4. Here
`λ_max(AᵀA) = ‖𝒜‖₂²` (the published `opNormA` is `‖𝒜‖₂`), and the bound is written without
division, so that `𝒜 = 0` gives the range `τ ∈ (0, ∞)` as on paper. -/
def StepRange {m n p : ℕ} (τ : ℝ) (Aop : Fin p → Mat m n) : Prop :=
  0 < τ ∧ τ * opNormA Aop ^ 2 < 2

/-- `X : ℕ → ℝ^{m×n}` is a run of the fixed point iterations (2.1), p. 7, from the arbitrary
starting point `X 0`: for every `k`, `Y^k = X^k − τ g(X^k) = h(X^k)` and
`X^{k+1} = S_{τμ}(Y^k)`, where `S_ν` is the matrix shrinkage operator (Definition 4, p. 8),
the published relation `IsShrink`. -/
def IsFixedPointRun {m n p : ℕ} (μ τ : ℝ) (Aop : Fin p → Mat m n) (b : Fin p → ℝ)
    (X : ℕ → Mat m n) : Prop :=
  ∀ k, IsShrink (τ * μ) (h τ Aop b (X k)) (X (k + 1))

end MaGoldfarbFPC.Convergence


