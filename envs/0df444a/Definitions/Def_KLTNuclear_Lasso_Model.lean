-- Prove2me | Definitions.Def_KLTNuclear_Lasso_Model
-- name    : KLTNuclear_Lasso_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:35.073213+00:00
-- url     : https://prove2.me/theorems/91e13aa5-9e78-4c36-86f8-e1fe5f032acb
-- title:
--   Fixed-design Gaussian regression, the noise vector M and the restricted constant μ_{c₀}(β) (witness form)
-- statement:
--   Let $x_1, \dots, x_n \in \mathbb R^p$ be a fixed design with design matrix $\mathbb X$.
--
--   1. **Noise vector.** For a noise vector $\xi = (\xi_1,\dots,\xi_n)$, put
--   $$
--   \mathbf M = \frac1n\sum_{i=1}^n \xi_i x_i \in \mathbb R^p .
--   $$
--   It is the diagonal of the matrix $\mathbf M$ of (2.2) when the design matrices $X_i = \operatorname{diag}(x_i)$ are fixed, and $\|\mathbf M\|_\infty = |\frac1n\sum_i\xi_ix_i|_\infty$.
--
--   2. **Restricted constant.** For $\beta \in \mathbb R^p$ with support $J = \{j : \beta(j)\neq 0\}$ and $c_0 \ge 0$, a number $\mu'$ is a **witness** for $\mu_{c_0}(\beta)$ if $\mu' > 0$ and
--   $$
--   |u_J|_2 \le \mu'\,\frac{1}{\sqrt n}\,|\mathbb X u|_2 \qquad\text{for all } u\in\mathbb R^p \text{ with } |u_{J^c}|_1 \le c_0|u_J|_1 .
--   $$
--   The paper's restricted constant is $\mu_{c_0}(\beta) = \mu_{c_0}(\operatorname{diag}\beta) = \inf\{\mu' : \mu' \text{ is a witness}\}$ (equal to $+\infty$ when there is none), and $\mu(\beta) = \mu_5(\beta)$.
--
--   3. **Gaussian noise.** On a probability space $(\Omega, P)$, the noise variables $\xi_1,\dots,\xi_n$ are measurable, independent, and each has law $\mathcal N(0,\sigma^2)$.
--
--   4. **Normalization.** The diagonal elements of the Gram matrix $\frac1n\mathbb X^\top\mathbb X$ are not larger than $1$: $\frac1n\sum_i x_i(j)^2 \le 1$ for every $j$.
--
--   These are the hypotheses and quantities of Theorem 14: $\mu(\beta)$ plays the role of a restricted eigenvalue at the support of $\beta$, and $\mathbf M$ is the stochastic term that the tuning parameter must dominate.
--
--   **Formalization Note** The paper defines $\mu_{c_0}(A)$ on p. 10 for a matrix $A$ in a linear subspace $\mathbb A$, through the projections $\mathcal P_A$, $\mathcal P_A^\perp$, the cone $\mathbb C_{A,c_0}$ and the $L_2(\Pi)$ norm. For $\mathbb A$ the diagonal matrices, $A = \operatorname{diag}\beta$, $B = \operatorname{diag}u$ and a fixed design, the paper computes on p. 26 that $\|\mathcal P_A(B)\|_2 = |u_J|_2$, $\|\mathcal P_A(B)\|_1 = |u_J|_1$, $\|\mathcal P_A^\perp(B)\|_1 = |u_{J^c}|_1$ and $\|B\|_{L_2(\Pi)} = n^{-1/2}|\mathbb Xu|_2$; the definition uses this vector form directly. The predicate records witnesses rather than the infimum: a real infimum of an empty set would be $0$, whereas the paper's value is $+\infty$, so every theorem is stated for every witness $\mu'$. Since the bounds are continuous and increasing in $\mu'$, this is equivalent to the infimum form. The noise law is `gaussianReal 0 (σ²)` with the variance as a nonnegative real.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 10 (μ_{c₀}(A), μ(A) = μ₅(A)), pp. 24–25 (§5.4: model Y_i = x_iᵀβ* + ξ_i, Gram normalization, μ_{c₀}(β)), p. 25 (proof of Theorem 14: ‖M‖∞ = |n⁻¹Σξ_ix_i|_∞), p. 26 (proof of Corollary 4: vector form of 𝒫_A, ℂ_{A,c₀}, ‖·‖_{L₂(Π)})

import Mathlib
import Definitions.Def_KLTNuclear_Lasso_Lasso

namespace KLTNuclear.Lasso

open MeasureTheory ProbabilityTheory

/-! The diagonal (vector) form of the objects of Theorem 2 and Theorem 14 of Koltchinskii,
Lounici and Tsybakov, arXiv:1011.6256v4: the noise vector **M** = (1/n) ∑ ξ_i x_i (p. 25), the
restricted constant μ_{c₀}(β) = μ_{c₀}(diag β) (pp. 10, 25, computed on p. 26) in witness form,
and the fixed-design Gaussian linear regression model Y_i = x_iᵀβ* + ξ_i (pp. 24–25). -/

/-- The vector `(1/n) ∑_i ξ_i x_i ∈ ℝ^p`, the diagonal of the matrix **M** of (2.2) for a fixed
design (p. 25); its `j`-th entry is `(1/n) ∑_i ξ_i x_i(j)`. -/
noncomputable def noiseVec {n p : ℕ} (x : Fin n → Fin p → ℝ) (ξ : Fin n → ℝ) : Fin p → ℝ :=
  fun j => (1 / (n : ℝ)) * ∑ i, ξ i * x i j

/-- `μ'` belongs to the set whose infimum is `μ_{c₀}(β)` (pp. 10, 25–26): `μ' > 0` and, with
`J = supp β`, `|u_J|_2 ≤ μ' n^{-1/2} |𝕏u|_2` for every `u ∈ ℝ^p` with `|u_{Jᶜ}|_1 ≤ c₀|u_J|_1`.
The paper's `μ_{c₀}(β)` is the infimum of all such `μ'` (`+∞` when there is none), and
`μ(β) = μ₅(β)`. -/
def IsMuWitness {n p : ℕ} (x : Fin n → Fin p → ℝ) (c₀ : ℝ) (β : Fin p → ℝ) (μ' : ℝ) : Prop :=
  0 < μ' ∧ ∀ u : Fin p → ℝ, l1On u (supp β)ᶜ ≤ c₀ * l1On u (supp β) →
    l2On u (supp β) ≤ μ' * (1 / Real.sqrt n) * l2Norm (design x u)

/-- The noise of the fixed-design regression of Theorem 14 (p. 25): `ξ_1, …, ξ_n` are
measurable, independent, and each has law `𝒩(0, σ²)`. -/
def IsGaussianNoise {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (ξ : Fin n → Ω → ℝ) (σ : ℝ) : Prop :=
  (∀ i, Measurable (ξ i)) ∧ iIndepFun ξ P ∧
    ∀ i, P.map (ξ i) = gaussianReal 0 (Real.toNNReal (σ ^ 2))

/-- The diagonal elements of the Gram matrix `(1/n)𝕏ᵀ𝕏` are not larger than `1` (p. 25):
`(1/n) ∑_i x_i(j)² ≤ 1` for every `j`. -/
def GramDiagLeOne {n p : ℕ} (x : Fin n → Fin p → ℝ) : Prop :=
  ∀ j : Fin p, (1 / (n : ℝ)) * ∑ i, x i j ^ 2 ≤ 1

end KLTNuclear.Lasso


