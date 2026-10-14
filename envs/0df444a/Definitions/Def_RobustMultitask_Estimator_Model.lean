-- Prove2me | Definitions.Def_RobustMultitask_Estimator_Model
-- name    : RobustMultitask_Estimator_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:40.03951+00:00
-- url     : https://prove2.me/theorems/b5e2f144-be83-4789-a106-e80d7ed1850c
-- title:
--   §2 and §4.1, pp. 8–9, 16 — the fixed-design multitask linear model with sparse heterogeneity, normalization (1), Assumption 1
-- statement:
--   This file sets up the fixed-design multitask linear model of Xu and Bastani.
--
--   **Tasks and data.** There are $N$ tasks. Task $j\in[N]$ has $n_j\ge 1$ observations and a deterministic design matrix $X^j\in\mathbb R^{n_j\times d}$, whose rows are the feature vectors. The columns are standardized as in (1):
--   $$\frac{1}{n_j}\big\|X^j_{(\cdot,i)}\big\|_2^2=1\qquad\text{for every } i\in[d].$$
--   The sample covariance matrix is $\widehat\Sigma^j=X^{j\top}X^j/n_j$.
--
--   **Sparse heterogeneity.** Each task has a parameter $\beta^j\in\mathbb R^d$ that decomposes as $\beta^j=\beta^\dagger+\delta^j$, where $\beta^\dagger$ is shared and $\|\delta^j\|_0\le s$ for all $j$.
--
--   **Noise and responses.** On a probability space $(\Omega,\mathbb P)$, the responses of task $j$ are
--   $$Y^j=X^j\beta^j+\epsilon^j\in\mathbb R^{n_j},$$
--   where each noise term $\epsilon^j_k$ is $\sigma_j$-subgaussian with mean zero (Definition 1: $\mathbb E[\exp(\lambda\epsilon^j_k)]\le\exp(\sigma_j^2\lambda^2/2)$ for every $\lambda\in\mathbb R$), $\sigma_j>0$, and all noise terms $\epsilon^j_k$, over all tasks $j$ and observations $k$, are mutually independent.
--
--   **Assumption 1 (Positive Definiteness).** For a constant $\psi>0$, $\lambda_{\min}(\widehat\Sigma^j)\ge\psi$ for every task $j\in[N]$.
--
--   These are the standing hypotheses of the paper's fixed-design results (§4.1), in particular of Proposition 5.
--
--   **Formalization Note** Tasks, coordinates and observations are `Fin N`, `Fin d`, `Fin (n j)`. The parameters are a family `β : Fin N → Fin d → ℝ` and `βdag`; the deviation $\delta^j$ is `β j - βdag`, so sparsity reads `l0 (β j - βdag) ≤ s`. Definition 1 with mean zero is Mathlib's `HasSubgaussianMGF (ε j k) (σ j ^ 2) P` (variance proxy $\sigma_j^2$, with $\sigma_j\in\mathbb R_{\ge 0}$); it includes integrability of every $e^{t\epsilon}$ and forces $\mathbb E\,\epsilon^j_k=0$. Independence is `iIndepFun` over the index type $\Sigma_j[n_j]$ of all pairs $(j,k)$. The model also requires $n_j\ge 1$ and $\sigma_j>0$, which the paper uses implicitly (it divides by $n_j$ and by $\sigma_j^2$). $\lambda_{\min}(\widehat\Sigma^j)\ge\psi$ is stated in Rayleigh-quotient form, $v^\top\widehat\Sigma^jv\ge\psi\|v\|_2^2$ for all $v$, which is equivalent for the symmetric $\widehat\Sigma^j$. `response X β ε j ω` is $Y^j$ at the sample point $\omega$.
-- source:
--   Xu & Bastani, Multitask Learning and Bandits via Robust Statistics, arXiv:2112.14233v5, pp. 8–9, §2 (Model, Definition 1, eq. (1)), and p. 16, §4.1 (Assumption 1)

import Mathlib
import Definitions.Def_RobustMultitask_Estimator_VectorNotation

namespace RobustMultitask.Estimator

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

/-- The sample covariance matrix `Σ̂ = XᵀX / m` of a design matrix `X ∈ ℝ^{m×d}` (§2, p. 9). -/
noncomputable def sampleCov {m d : ℕ} (X : Matrix (Fin m) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  (1 / (m : ℝ)) • (Xᵀ * X)

/-- `λ_min(Σ) ≥ ψ`, in Rayleigh-quotient form: `vᵀ Σ v ≥ ψ ‖v‖₂²` for every `v ∈ ℝᵈ`. For a
symmetric matrix such as `Σ̂ = XᵀX/m` this is equivalent to the smallest eigenvalue being at
least `ψ`. -/
def MinEigAtLeast {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (ψ : ℝ) : Prop :=
  ∀ v : Fin d → ℝ, ψ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (S *ᵥ v)

/-- **Assumption 1 (Positive Definiteness)** (p. 16): there is a constant `ψ > 0` such that
`λ_min(Σ̂ʲ) ≥ ψ` for every task `j ∈ [N]`. Stated for a given `ψ`. -/
def Assumption1 {N d : ℕ} (n : Fin N → ℕ) (X : (j : Fin N) → Matrix (Fin (n j)) (Fin d) ℝ)
    (ψ : ℝ) : Prop :=
  0 < ψ ∧ ∀ j, MinEigAtLeast (sampleCov (X j)) ψ

/-- The fixed-design multitask linear model with sparse heterogeneity (§2, pp. 8–9).

* `N` tasks (`Fin N`), dimension `d` (`Fin d`), task `j` has `n j ≥ 1` observations (`Fin (n j)`).
* Deterministic design matrices `X j ∈ ℝ^{n_j × d}`, standardized as in (1):
  `(1/n_j) ‖Xʲ_(·,i)‖₂² = 1` for every column `i`.
* Task parameters `β j = β† + δʲ` with `‖δʲ‖₀ ≤ s`; here `δʲ` is `β j - βdag`.
* Noise `ε j k : Ω → ℝ` on the probability space `(Ω, P)`: each `ε j k` is `σ_j`-subgaussian with
  mean zero (Definition 1 with `µ = 0`, i.e. Mathlib's `HasSubgaussianMGF` with variance proxy
  `σ_j²`), `σ_j > 0`, and all noise terms `ε j k`, over all pairs `(j, k)`, are mutually
  independent.

The responses are `Yʲ = Xʲ βʲ + εʲ` (`response`). -/
structure IsMultitaskModel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {N d : ℕ}
    (n : Fin N → ℕ) (X : (j : Fin N) → Matrix (Fin (n j)) (Fin d) ℝ)
    (β : Fin N → Fin d → ℝ) (βdag : Fin d → ℝ) (s : ℕ) (σ : Fin N → ℝ≥0)
    (ε : (j : Fin N) → Fin (n j) → Ω → ℝ) : Prop where
  pos_n : ∀ j, 0 < n j
  standardized : ∀ j (i : Fin d), (1 / (n j : ℝ)) * ∑ k, X j k i ^ 2 = 1
  sparse : ∀ j, l0 (β j - βdag) ≤ s
  pos_σ : ∀ j, 0 < σ j
  subgaussian : ∀ j k, HasSubgaussianMGF (ε j k) (σ j ^ 2) P
  indep : iIndepFun (fun p : (Σ j : Fin N, Fin (n j)) => ε p.1 p.2) P

/-- The response vector `Yʲ = Xʲ βʲ + εʲ ∈ ℝ^{n_j}` of task `j` at the sample point `ω`. -/
def response {Ω : Type*} {N d : ℕ} {n : Fin N → ℕ}
    (X : (j : Fin N) → Matrix (Fin (n j)) (Fin d) ℝ) (β : Fin N → Fin d → ℝ)
    (ε : (j : Fin N) → Fin (n j) → Ω → ℝ) (j : Fin N) (ω : Ω) : Fin (n j) → ℝ :=
  X j *ᵥ β j + fun k => ε j k ω

end RobustMultitask.Estimator


