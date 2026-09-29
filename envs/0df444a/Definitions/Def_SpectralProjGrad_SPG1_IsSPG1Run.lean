-- Prove2me | Definitions.Def_SpectralProjGrad_SPG1_IsSPG1Run
-- name    : SpectralProjGrad_SPG1_IsSPG1Run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:49:03.255739+00:00
-- url     : https://prove2.me/theorems/95a566eb-20a0-4e4e-91f7-a339bc00d061
-- title:
--   An infinite run of Algorithm SPG1 (Algorithm 2.1)
-- statement:
--   Fix a set $\Omega\subseteq\mathbb R^n$, an objective $f$ with gradient $g=\nabla f$, a map $P$ (the orthogonal projection onto $\Omega$), an integer $M$ and reals $\alpha_{\min},\alpha_{\max},\gamma,\sigma_1,\sigma_2$. A pair of sequences $(x_k)_{k\ge0}$ in $\mathbb R^n$ and $(\alpha_k)_{k\ge0}$ in $\mathbb R$ is an **infinite run of SPG1** (Algorithm 2.1 of Birgin, Martínez and Raydan) when:
--
--   1. $x_0\in\Omega$ and $\alpha_0\in[\alpha_{\min},\alpha_{\max}]$.
--   2. *Step 1 never stops:* $\|P(x_k-g(x_k))-x_k\|\neq0$ for every $k$.
--   3. *Step 2 (backtracking along the projection arc):* for every $k$ there are trial steps $\mu_0=\alpha_k,\mu_1,\dots,\mu_m$ with $\mu_{i+1}\in[\sigma_1\mu_i,\sigma_2\mu_i]$ (rule (2)), such that, writing $x_+(\lambda)=P(x_k-\lambda g(x_k))$, the nonmonotone Armijo test
--   $$
--   f(x_+(\lambda))\le\max_{0\le j\le\min\{k,M-1\}} f(x_{k-j})+\gamma\,\langle x_+(\lambda)-x_k,\,g(x_k)\rangle \tag{1}
--   $$
--   fails at $\lambda=\mu_0,\dots,\mu_{m-1}$ and holds at $\lambda=\mu_m$; and $x_{k+1}=x_+(\mu_m)$.
--   4. *Step 3 (safeguarded spectral step):* with $s_k=x_{k+1}-x_k$, $y_k=g(x_{k+1})-g(x_k)$ and $b_k=\langle s_k,y_k\rangle$, one has $\alpha_{k+1}=\alpha_{\max}$ if $b_k\le0$ and $\alpha_{k+1}=\min\{\alpha_{\max},\max\{\alpha_{\min},\langle s_k,s_k\rangle/b_k\}\}$ otherwise.
--
--   This packages the whole trajectory of SPG1 when it never terminates; the first trial of each backtracking is the spectral step $\alpha_k$, and the sufficient-decrease term in (1) carries no factor $\lambda$.
--
--   **Formalization Note** The choice $\lambda_{new}\in[\sigma_1\lambda,\sigma_2\lambda]$ in (2) is arbitrary in the paper, so the run records one admissible finite trial trace per iteration; the conditions that earlier trials fail and the last one succeeds are part of the predicate. Iterations are indexed from $0$. The auxiliary definitions `SPG1Test` (test (1)) and `spectralStep` (Step 3) live in the same file.
-- source:
--   Birgin, Martínez & Raydan, Nonmonotone Spectral Projected Gradient Methods on Convex Sets, authors' updated version (July 2004) of SIAM J. Optim. 10(4) (2000), https://www.ime.unicamp.br/~martinez/bmr.pdf, p. 3, Algorithm 2.1 (Steps 1–3, test (1), rule (2)); p. 4 ("called SPG1 from now on")

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_nonmonotoneRef

namespace SpectralProjGrad.SPG1

/-- The nonmonotone Armijo test (1) of SPG1 at iteration `k` for the trial step `lam`, along the
projection arc: with the trial point `x₊ = P(x_k - lam g(x_k))`,
`f(x₊) ≤ max_{0≤j≤min{k,M-1}} f(x_{k-j}) + γ ⟨x₊ - x_k, g(x_k)⟩`
(no factor `lam` in the last term). -/
def SPG1Test {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (M : ℕ) (γ : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ) (lam : ℝ) : Prop :=
  f (P (x k - lam • gradient f (x k))) ≤
    SpectralProjGrad.Shared.nonmonotoneRef f x M k + γ * inner ℝ (P (x k - lam • gradient f (x k)) - x k) (gradient f (x k))

/-- Step 3 of Algorithm 2.1 (the safeguarded spectral step): with `b = ⟨s, y⟩`, return `α_max`
if `b ≤ 0`, and otherwise `min {α_max, max {α_min, ⟨s, s⟩ / b}}`. -/
noncomputable def spectralStep {n : ℕ} (αmin αmax : ℝ) (s y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if inner ℝ s y ≤ 0 then αmax else min αmax (max αmin (inner ℝ s s / inner ℝ s y))

/-- `(x, α)` is an infinite run of Algorithm SPG1 (Algorithm 2.1) on `Ω`, for the objective `f`
with gradient `g = ∇f`, the projection `P`, and the parameters `M, α_min, α_max, γ, σ₁, σ₂`;
iterations are indexed from `0`.

* `x₀ ∈ Ω` and `α₀ ∈ [α_min, α_max]`.
* Step 1 never stops: `‖P(x_k - g(x_k)) - x_k‖ ≠ 0` for every `k`.
* Step 2: at every iteration `k` there is a finite backtracking trace `μ_0 = α_k, μ_1, …, μ_m`
  with `μ_{i+1} ∈ [σ₁ μ_i, σ₂ μ_i]` (rule (2)), test (1) fails at `μ_0, …, μ_{m-1}` and holds at
  `μ_m`, and `x_{k+1} = P(x_k - μ_m g(x_k))`.
* Step 3: `α_{k+1}` is the safeguarded spectral step for `s_k = x_{k+1} - x_k` and
  `y_k = g(x_{k+1}) - g(x_k)`. -/
structure IsSPG1Run {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : ℕ) (αmin αmax γ σ₁ σ₂ : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (α : ℕ → ℝ) : Prop where
  start_mem : x 0 ∈ Ω
  start_step : α 0 ∈ Set.Icc αmin αmax
  step1_not_stop : ∀ k, ‖P (x k - gradient f (x k)) - x k‖ ≠ 0
  step2_backtrack : ∀ k, ∃ (m : ℕ) (μ : ℕ → ℝ),
    μ 0 = α k ∧
    (∀ i < m, σ₁ * μ i ≤ μ (i + 1) ∧ μ (i + 1) ≤ σ₂ * μ i) ∧
    (∀ i < m, ¬ SPG1Test f P M γ x k (μ i)) ∧
    SPG1Test f P M γ x k (μ m) ∧
    x (k + 1) = P (x k - μ m • gradient f (x k))
  step3_spectral : ∀ k,
    α (k + 1) = spectralStep αmin αmax (x (k + 1) - x k) (gradient f (x (k + 1)) - gradient f (x k))

end SpectralProjGrad.SPG1


