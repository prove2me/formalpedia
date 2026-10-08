-- Prove2me | Definitions.Def_StochKriging_OptimalMSE_Model
-- name    : StochKriging_OptimalMSE_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T23:06:14.078001+00:00
-- url     : https://prove2.me/theorems/6c836be4-d8df-4d53-ab4b-1f45f72e98a1
-- title:
--   §2, pp. 363–364 — the second-order stochastic kriging model (3), sample means (4), Σ_M, Σ_ε, linear predictors (5), the optimal MSE and the predictor (6)
-- statement:
--   Fix a probability space $(\Omega,\mathcal F,P)$ and a set $\mathcal X$ of design settings. A **stochastic simulation** at a setting $\mathbf x\in\mathcal X$ produces on replication $j=1,2,\dots$ the output
--   $$\mathcal Y_j(\mathbf x)=\beta_0+\mathsf M(\mathbf x)+\varepsilon_j(\mathbf x),$$
--   which is model (3) with the trend $\mathbf f(\mathbf x)^\top\beta=\beta_0$. Here $\beta_0\in\mathbb R$ is the overall surface mean, $\mathsf M$ is a random field (the **extrinsic** uncertainty) and $\varepsilon_j(\mathbf x)$ is the sampling noise of replication $j$ (the **intrinsic** uncertainty). The **second-order model** assumes:
--   1. every $\mathsf M(\mathbf x)$ and every $\varepsilon_j(\mathbf x)$ has a finite second moment;
--   2. $\mathsf M(\mathbf x)$ has mean $0$ and $\varepsilon_j(\mathbf x)$ has mean $0$, for all $\mathbf x$ and $j$;
--   3. the field and the noise are uncorrelated: $\mathrm{Cov}[\mathsf M(\mathbf x),\varepsilon_j(\mathbf x')]=0$ for all $\mathbf x,\mathbf x',j$.
--
--   Nothing else is assumed about the noise: its variance may depend on $\mathbf x$, and noises at different settings may be correlated, which models **common random numbers** (CRN).
--
--   An **experiment design** is a list of pairs $(\mathbf x_i,n_i)$, $i=1,\dots,k$. The **sample mean** (4) at $\mathbf x_i$ and the vector of sample means are
--   $$\bar{\mathcal Y}(\mathbf x_i)=\frac1{n_i}\sum_{j=1}^{n_i}\mathcal Y_j(\mathbf x_i),\qquad \bar{\mathcal Y}=\big(\bar{\mathcal Y}(\mathbf x_1),\dots,\bar{\mathcal Y}(\mathbf x_k)\big)^\top .$$
--   The quantity to predict at a point $\mathbf x_0$ is the noise-free response $\mathsf Y(\mathbf x_0)=\beta_0+\mathsf M(\mathbf x_0)$.
--
--   The covariances of §2 are $\Sigma_{\mathsf M}(\mathbf x,\mathbf x')=\mathrm{Cov}[\mathsf M(\mathbf x),\mathsf M(\mathbf x')]$; the $k\times k$ matrix $\Sigma_{\mathsf M}=\big(\Sigma_{\mathsf M}(\mathbf x_h,\mathbf x_i)\big)_{h,i}$; the vector $\Sigma_{\mathsf M}(\mathbf x_0,\cdot)=\big(\mathrm{Cov}[\mathsf M(\mathbf x_0),\mathsf M(\mathbf x_i)]\big)_{i=1}^k$; and the $k\times k$ matrix $\Sigma_\varepsilon$ with $(h,i)$ entry
--   $$\mathrm{Cov}\Big[\sum_{j=1}^{n_h}\varepsilon_j(\mathbf x_h)/n_h,\ \sum_{j=1}^{n_i}\varepsilon_j(\mathbf x_i)/n_i\Big].$$
--
--   A **linear predictor** of the form (5) is $\lambda_0+\lambda^\top\bar{\mathcal Y}$ with weights $\lambda_0\in\mathbb R$, $\lambda\in\mathbb R^k$. The **mean squared error** of a predictor $\hat P$ of $\mathsf Y(\mathbf x_0)$ is $\mathrm E[(\hat P-\mathsf Y(\mathbf x_0))^2]$, and the **optimal MSE** is the infimum of the MSE over all weights:
--   $$\mathrm{MSE}^\star(\mathbf x_0)=\inf_{(\lambda_0,\lambda)\in\mathbb R\times\mathbb R^k}\mathrm E\big[(\lambda_0+\lambda^\top\bar{\mathcal Y}-\mathsf Y(\mathbf x_0))^2\big].$$
--   The **stochastic kriging predictor** (6) is
--   $$\widehat{\mathsf Y}(\mathbf x_0)=\beta_0+\Sigma_{\mathsf M}(\mathbf x_0,\cdot)^\top\,[\Sigma_{\mathsf M}+\Sigma_\varepsilon]^{-1}\,(\bar{\mathcal Y}-\beta_0\mathbf 1_k),$$
--   where $\mathbf 1_k$ is the vector of ones.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The settings form an arbitrary type `X` (the paper's $\mathbb R^d$); only the design points and $\mathbf x_0$ enter. Design points are indexed by `Fin k` (the paper's $i$ is `i.val + 1`), and replication $j\ge1$ of the paper is index `j - 1`, so the sums in (4) and in $\Sigma_\varepsilon$ run over `Finset.range (n i)`. With $n_i=0$ the Lean sample mean is $0$; every theorem assumes $n_i\ge1$. Covariances are Mathlib's `ProbabilityTheory.covariance`, expectations Bochner integrals (finite second moments make every MSE integrable). The uncorrelatedness of field and noise is not written in §2; it is the second-order content of Assumption 1's "independent of $\mathsf M$" (p. 365), and without it the covariance of $\bar{\mathcal Y}$ is not $\Sigma_{\mathsf M}+\Sigma_\varepsilon$. The infimum is over a nonempty set of nonnegative reals, so it is a genuine infimum. Lean's matrix inverse is $0$ for a singular matrix; every theorem using (6) assumes the matrices are positive definite, so the inverse is genuine.
-- source:
--   Ankenman, Nelson, Staum, Stochastic Kriging for Simulation Metamodeling, Proc. 2008 Winter Simulation Conference, pp. 363–364, §2, displays (3), (4), (5), (6), the definitions of Σ_M, Σ_M(x₀,·), Σ_ε and the MSE

import Mathlib

open MeasureTheory ProbabilityTheory Matrix

namespace StochKriging.OptimalMSE

/-- The second-order assumptions of the stochastic kriging model (3) of Ankenman, Nelson and
Staum (WSC 2008, §2, p. 363), with `f(x)ᵀβ = β₀`. The simulation output on replication `j`
(0-based; the paper's replication `j + 1`) at the point `x` is `β₀ + M x + ε j x`.

* `M x` is the extrinsic random field at `x`: square integrable with mean 0
  ("M is a realization of a mean 0 random field", p. 363).
* `ε j x` is the intrinsic noise of replication `j` at `x`: square integrable with mean 0
  ("εj(x) has mean 0", p. 363). No independence, no identical distribution and no
  independence across design points is assumed: common random numbers (CRN) are allowed.
* The field and the noise are uncorrelated. §2 does not state this; it is the second-order
  content of Assumption 1's "independent of M" (p. 365) and is needed for `Cov(Ȳ) = ΣM + Σε`. -/
structure IsModel {Ω X : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : X → Ω → ℝ) (ε : ℕ → X → Ω → ℝ) : Prop where
  memLp_field : ∀ x, MemLp (M x) 2 P
  memLp_noise : ∀ j x, MemLp (ε j x) 2 P
  mean_field : ∀ x, ∫ ω, M x ω ∂P = 0
  mean_noise : ∀ j x, ∫ ω, ε j x ω ∂P = 0
  uncorrelated : ∀ x x' j, cov[M x, ε j x'; P] = 0

variable {Ω X : Type*} [MeasurableSpace Ω] {k : ℕ}

/-- Display (3) with `f(x)ᵀβ = β₀`: the output `𝒴_{j+1}(x) = β₀ + M(x) + ε_{j+1}(x)` of
replication `j + 1` (Lean index `j`) at `x`. -/
def output (β₀ : ℝ) (M : X → Ω → ℝ) (ε : ℕ → X → Ω → ℝ) (j : ℕ) (x : X) : Ω → ℝ :=
  fun ω => β₀ + M x ω + ε j x ω

/-- Display (4): the vector of sample means `Ȳ = (Ȳ(x₁), …, Ȳ(x_k))`, where
`Ȳ(x_i) = (1/n_i) Σ_{j=1}^{n_i} 𝒴_j(x_i)`. Design point `x_{i+1}` of the paper is `x i`. -/
noncomputable def sampleMean (β₀ : ℝ) (M : X → Ω → ℝ) (ε : ℕ → X → Ω → ℝ) (x : Fin k → X)
    (n : Fin k → ℕ) : Ω → Fin k → ℝ :=
  fun ω i => (1 / (n i : ℝ)) * ∑ j ∈ Finset.range (n i), output β₀ M ε j (x i) ω

/-- The prediction target `Y(x₀) = β₀ + M(x₀)` (no noise), p. 363. -/
def target (β₀ : ℝ) (M : X → Ω → ℝ) (x₀ : X) : Ω → ℝ :=
  fun ω => β₀ + M x₀ ω

/-- The averaged noise `Σ_{j=1}^{n_i} ε_j(x_i) / n_i` at design point `i`. -/
noncomputable def avgNoise (ε : ℕ → X → Ω → ℝ) (x : Fin k → X) (n : Fin k → ℕ) (i : Fin k) : Ω → ℝ :=
  fun ω => (∑ j ∈ Finset.range (n i), ε j (x i) ω) / (n i : ℝ)

/-- `ΣM(x, x') = Cov[M(x), M(x')]`, p. 364. -/
noncomputable def SigmaMFun (P : Measure Ω) (M : X → Ω → ℝ) (x x' : X) : ℝ :=
  cov[M x, M x'; P]

/-- `ΣM`: the `k × k` covariance matrix of the field across the design points, p. 364. -/
noncomputable def SigmaM (P : Measure Ω) (M : X → Ω → ℝ) (x : Fin k → X) :
    Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun h i => SigmaMFun P M (x h) (x i)

/-- `ΣM(x₀, ·) = (Cov[M(x₀), M(x₁)], …, Cov[M(x₀), M(x_k)])ᵀ`, p. 364. -/
noncomputable def SigmaMCross (P : Measure Ω) (M : X → Ω → ℝ) (x : Fin k → X) (x₀ : X) :
    Fin k → ℝ :=
  fun i => SigmaMFun P M x₀ (x i)

/-- `Σε`: the `k × k` matrix with `(h, i)` entry
`Cov[Σ_{j=1}^{n_h} ε_j(x_h)/n_h, Σ_{j=1}^{n_i} ε_j(x_i)/n_i]`, p. 364. -/
noncomputable def SigmaEps (P : Measure Ω) (ε : ℕ → X → Ω → ℝ) (x : Fin k → X)
    (n : Fin k → ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun h i => cov[avgNoise ε x n h, avgNoise ε x n i; P]

/-- Display (5): the linear predictor `λ₀ + λᵀȲ` with weights `λ₀ ∈ ℝ`, `λ ∈ ℝᵏ`. -/
def linPred (l₀ : ℝ) (l : Fin k → ℝ) (Ybar : Ω → Fin k → ℝ) : Ω → ℝ :=
  fun ω => l₀ + l ⬝ᵥ Ybar ω

/-- Mean squared error `E[(P̂ − Y)²]` of a predictor `P̂` of a target `Y`. -/
noncomputable def mse (P : Measure Ω) (pred tgt : Ω → ℝ) : ℝ :=
  ∫ ω, (pred ω - tgt ω) ^ 2 ∂P

/-- The optimal MSE over all predictors of the form (5): the infimum, over every
`(λ₀, λ) ∈ ℝ × ℝᵏ`, of `E[(λ₀ + λᵀȲ − Y(x₀))²]`. -/
noncomputable def optimalMSE (P : Measure Ω) (β₀ : ℝ) (M : X → Ω → ℝ)
    (ε : ℕ → X → Ω → ℝ) (x : Fin k → X) (n : Fin k → ℕ) (x₀ : X) : ℝ :=
  ⨅ p : ℝ × (Fin k → ℝ), mse P (linPred p.1 p.2 (sampleMean β₀ M ε x n)) (target β₀ M x₀)

/-- Display (6): the stochastic kriging predictor
`Ŷ(x₀) = β₀ + ΣM(x₀, ·)ᵀ [ΣM + Σε]⁻¹ (Ȳ − β₀ 1_k)`. -/
noncomputable def skPredictor (P : Measure Ω) (β₀ : ℝ) (M : X → Ω → ℝ)
    (ε : ℕ → X → Ω → ℝ) (x : Fin k → X) (n : Fin k → ℕ) (x₀ : X) : Ω → ℝ :=
  fun ω => β₀ + SigmaMCross P M x x₀ ⬝ᵥ
    ((SigmaM P M x + SigmaEps P ε x n)⁻¹ *ᵥ (sampleMean β₀ M ε x n ω - β₀ • fun _ => 1))

end StochKriging.OptimalMSE


