-- Prove2me | Definitions.Def_WainwrightHDS_NucNorm_singVal
-- name    : WainwrightHDS_NucNorm_singVal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:25:23.562398+00:00
-- url     : https://prove2.me/theorems/e2552f3f-2eaa-46d6-8e06-5d6347ddf854
-- title:
--   Singular values $\sigma_1(\Theta)\ge\sigma_2(\Theta)\ge\dots\ge\sigma_{d'}(\Theta)\ge 0$
-- statement:
--   Let $\Theta\in\mathbb R^{d_1\times d_2}$ and $d'=\min\{d_1,d_2\}$. Writing the singular value decomposition $\Theta=UDV^\top$ with $U\in\mathbb R^{d_1\times d'}$, $V\in\mathbb R^{d_2\times d'}$ orthonormal and $D\in\mathbb R^{d'\times d'}$ diagonal, the diagonal entries of $D$ are the **singular values** of $\Theta$, listed in non-increasing order:
--
--   $$
--   \sigma_1(\Theta)\ \ge\ \sigma_2(\Theta)\ \ge\ \cdots\ \ge\ \sigma_{d'}(\Theta)\ \ge\ 0 .
--   $$
--
--   Equivalently, $\sigma_j(\Theta)$ is the square root of the $j$-th largest eigenvalue of $\Theta^\top\Theta$. The nuclear norm is their sum, and tails of this sorted sequence measure how far $\Theta$ is from having rank $r$.
--
--   **Formalization Note** The value is Mathlib's `LinearMap.singularValues` of the linear map $z\mapsto\Theta z$ from $\mathbb R^{d_2}$ to $\mathbb R^{d_1}$, which is sorted non-increasingly and indexed from $0$: the book's $\sigma_j(\Theta)$, $j=1,\dots,d'$, is the Lean value at index $j-1$. Values at indices $\ge d'$ are $0$.
-- source:
--   Wainwright, High-Dimensional Statistics: A Non-Asymptotic Viewpoint, Cambridge University Press 2019, doi:10.1017/9781108627771, §9.2, p. 268 (PDF p. 288), Eqs. (9.17)–(9.18)

import Mathlib

namespace WainwrightHDS.NucNorm

/-- **Singular values** `σ₁(Θ) ≥ σ₂(Θ) ≥ ⋯ ≥ σ_{d'}(Θ) ≥ 0` of `Θ ∈ ℝ^{d₁×d₂}`, `d' = min{d₁, d₂}`.
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, §9.2, p. 268 (PDF p. 288), Eqs. (9.17)–(9.18).

`singVal j Θ` is Mathlib's `LinearMap.singularValues` of the linear map `z ↦ Θ z` from
`ℝ^{d₂}` to `ℝ^{d₁}` (Euclidean spaces): the square roots of the eigenvalues of `ΘᵀΘ` in
non-increasing order (`LinearMap.singularValues_antitone`), and `0` from index `rank Θ` on.

Formalization Note: indexing is **0-based**: the book's `σ_j(Θ)`, `j = 1, …, d'`, is
`singVal (j - 1) Θ`. Mathlib lists `d₂` values (the dimension of the domain), of which those with
index `≥ min d₁ d₂` are `0` because `rank Θ ≤ min d₁ d₂`. -/
noncomputable def singVal {d₁ d₂ : ℕ} (j : ℕ) (Θ : Matrix (Fin d₁) (Fin d₂) ℝ) : ℝ :=
  (Matrix.toEuclideanLin Θ).singularValues j

end WainwrightHDS.NucNorm


