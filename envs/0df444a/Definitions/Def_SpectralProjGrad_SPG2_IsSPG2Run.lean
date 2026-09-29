-- Prove2me | Definitions.Def_SpectralProjGrad_SPG2_IsSPG2Run
-- name    : SpectralProjGrad_SPG2_IsSPG2Run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:59:38.742988+00:00
-- url     : https://prove2.me/theorems/5b89c7f4-e2a3-4518-a1cb-6d28b6831de8
-- title:
--   Infinite run of Algorithm SPG2 (nonmonotone spectral projected gradient)
-- statement:
--   Fix a set $\Omega\subseteq\mathbb R^n$, an objective $f$ with gradient $g=\nabla f$, the orthogonal projection $P$ onto $\Omega$, an integer $M$ and reals $\alpha_{\min},\alpha_{\max},\gamma,\sigma_1,\sigma_2$. A pair of sequences $(x_k)_{k\ge0}$ in $\mathbb R^n$ and $(\alpha_k)_{k\ge0}$ in $\mathbb R$ is an **infinite run of SPG2** (Algorithm 2.1 with the backtracking step of Algorithm 2.2) if:
--
--   1. **Start.** $x_0\in\Omega$ and $\alpha_0\in[\alpha_{\min},\alpha_{\max}]$.
--   2. **Step 1 never stops.** $\|P(x_k-g(x_k))-x_k\|\ne0$ for every $k$.
--   3. **Step 2 (backtracking).** Let $d_k=P(x_k-\alpha_k g(x_k))-x_k$ and $R_k=\max_{0\le j\le\min\{k,M-1\}}f(x_{k-j})$. For every $k$ there are trial steps $\lambda^{(0)}=1,\lambda^{(1)},\dots,\lambda^{(m)}$ with $\lambda^{(i+1)}\in[\sigma_1\lambda^{(i)},\sigma_2\lambda^{(i)}]$ (rule (2)) such that the nonmonotone Armijo test
--   $$
--   f(x_k+\lambda d_k)\le R_k+\gamma\lambda\langle d_k,g(x_k)\rangle \tag{3}
--   $$
--   fails for $\lambda=\lambda^{(0)},\dots,\lambda^{(m-1)}$ and holds for $\lambda=\lambda^{(m)}$; then $\lambda_k=\lambda^{(m)}$ and $x_{k+1}=x_k+\lambda_k d_k$.
--   4. **Step 3 (spectral step).** With $s_k=x_{k+1}-x_k$ and $y_k=g(x_{k+1})-g(x_k)$, $b_k=\langle s_k,y_k\rangle$: if $b_k\le0$ then $\alpha_{k+1}=\alpha_{\max}$, and otherwise $\alpha_{k+1}=\min\{\alpha_{\max},\max\{\alpha_{\min},\langle s_k,s_k\rangle/b_k\}\}$.
--
--   The choice of each $\lambda^{(i+1)}$ inside $[\sigma_1\lambda^{(i)},\sigma_2\lambda^{(i)}]$ is free, so this predicate describes every sequence the algorithm can produce, for every implementation of rule (2). Runs that stop at Step 1 are finite and are not described.
--
--   **Formalization Note** Iterations are 0-based. The auxiliary definitions `SPG2Test` (test (3)) and `spectralStep` (Step 3) live in the same file. The parameter constraints $M\ge1$, $0<\alpha_{\min}<\alpha_{\max}$, $\gamma\in(0,1)$, $0<\sigma_1<\sigma_2<1$ are hypotheses of the theorems, not fields of the predicate.
-- source:
--   Birgin, Martínez & Raydan, Nonmonotone Spectral Projected Gradient Methods on Convex Sets, authors' updated version (July 2004) of SIAM J. Optim. 10(4) (2000), https://www.ime.unicamp.br/~martinez/bmr.pdf, p. 3 (parameters; Algorithm 2.1 Steps 1 and 3, rule (2)) and p. 4 (Algorithm 2.2: Step 2, eq. (3))

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_scaledProjGrad
import Definitions.Def_SpectralProjGrad_Shared_nonmonotoneRef

namespace SpectralProjGrad.SPG2

/-- The nonmonotone Armijo test (3) of SPG2 at iteration `k` for the trial step `lam`:
`f(x_k + lam d_k) ≤ max_{0≤j≤min{k,M-1}} f(x_{k-j}) + γ lam ⟨d_k, g(x_k)⟩`, where
`d_k = P(x_k - α_k g(x_k)) - x_k`. -/
def SPG2Test {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (M : ℕ) (γ : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (α : ℕ → ℝ) (k : ℕ) (lam : ℝ) : Prop :=
  f (x k + lam • SpectralProjGrad.Shared.scaledProjGrad P f (α k) (x k)) ≤
    SpectralProjGrad.Shared.nonmonotoneRef f x M k + γ * lam * inner ℝ (SpectralProjGrad.Shared.scaledProjGrad P f (α k) (x k)) (gradient f (x k))

/-- Step 3 of Algorithm 2.1 (the safeguarded spectral step): with `b = ⟨s, y⟩`, return `α_max`
if `b ≤ 0`, and otherwise `min {α_max, max {α_min, ⟨s, s⟩ / b}}`. -/
noncomputable def spectralStep {n : ℕ} (αmin αmax : ℝ) (s y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if inner ℝ s y ≤ 0 then αmax else min αmax (max αmin (inner ℝ s s / inner ℝ s y))

/-- `(x, α)` is an infinite run of Algorithm SPG2 (Algorithm 2.1 with the backtracking Step 2 of
Algorithm 2.2) on `Ω`, for the objective `f` with gradient `g = ∇f`, the projection `P`, and the
parameters `M, α_min, α_max, γ, σ₁, σ₂`; iterations are indexed from `0`.

* `x₀ ∈ Ω` and `α₀ ∈ [α_min, α_max]`.
* Step 1 never stops: `‖P(x_k - g(x_k)) - x_k‖ ≠ 0` for every `k`.
* Step 2: at every iteration `k` there is a finite backtracking trace `μ_0 = 1, μ_1, …, μ_m` with
  `μ_{i+1} ∈ [σ₁ μ_i, σ₂ μ_i]` (rule (2)), test (3) fails at `μ_0, …, μ_{m-1}` and holds at `μ_m`,
  and `x_{k+1} = x_k + μ_m d_k` with `d_k = P(x_k - α_k g(x_k)) - x_k`.
* Step 3: `α_{k+1}` is the safeguarded spectral step for `s_k = x_{k+1} - x_k` and
  `y_k = g(x_{k+1}) - g(x_k)`. -/
structure IsSPG2Run {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : ℕ) (αmin αmax γ σ₁ σ₂ : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (α : ℕ → ℝ) : Prop where
  start_mem : x 0 ∈ Ω
  start_step : α 0 ∈ Set.Icc αmin αmax
  step1_not_stop : ∀ k, ‖P (x k - gradient f (x k)) - x k‖ ≠ 0
  step2_backtrack : ∀ k, ∃ (m : ℕ) (μ : ℕ → ℝ),
    μ 0 = 1 ∧
    (∀ i < m, σ₁ * μ i ≤ μ (i + 1) ∧ μ (i + 1) ≤ σ₂ * μ i) ∧
    (∀ i < m, ¬ SPG2Test f P M γ x α k (μ i)) ∧
    SPG2Test f P M γ x α k (μ m) ∧
    x (k + 1) = x k + μ m • SpectralProjGrad.Shared.scaledProjGrad P f (α k) (x k)
  step3_spectral : ∀ k,
    α (k + 1) = spectralStep αmin αmax (x (k + 1) - x k) (gradient f (x (k + 1)) - gradient f (x k))

end SpectralProjGrad.SPG2


