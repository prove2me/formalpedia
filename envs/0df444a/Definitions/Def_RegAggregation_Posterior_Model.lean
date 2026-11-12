-- Prove2me | Definitions.Def_RegAggregation_Posterior_Model
-- name    : RegAggregation_Posterior_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:12.955777+00:00
-- url     : https://prove2.me/theorems/fcd0e91d-70ef-447a-9038-d3bb3330480a
-- title:
--   §2.2, §3.2, pp. 8–17 — exchangeable Gaussian forecast model: P(K), Σ, Λ22, η1, η2, Gaussian likelihood of the probit predictions, prior family π(θ; a, b), Fisher information
-- statement:
--   This file sets up the exchangeable Gaussian model of forecast aggregation of Satopää (2022). There are $K \ge 2$ forecasters. Each reports a probability $p_k$ for a binary event; the analysis works with the **probit predictions** $P_k = \Phi^{-1}(p_k) \in \mathbb R$, collected in $\mathbf P = (P_1,\dots,P_K) \in \mathbb R^K$. The **common prior** is $p_0 = \Phi(\mu_0)$ with $\mu_0 \in \mathbb R$, where $\Phi$ is the standard normal distribution function.
--
--   The model has three parameters $\theta = (\delta, \gamma, \rho)$: $\delta$ is the variance of each forecaster's latent variable, $\gamma$ the variance of the information each forecaster holds, and $\rho$ the covariance between any two forecasters' information. The following objects are defined.
--
--   1. The **parameter space** of Theorem 2.1,
--   $$\mathcal P(K) = \Big\{(\delta,\gamma,\rho) : \max\Big\{0, \tfrac{K\gamma^2-\gamma}{K-1}\Big\} \le \rho < \gamma \le \delta\Big\}.$$
--   2. The **covariance matrix of the evidence** $(I_0, I_1, \dots, I_K)$,
--   $$\Sigma = \begin{pmatrix} 1 & \gamma \mathbf 1_K' \\ \gamma \mathbf 1_K & (\gamma-\rho) I_K + \rho J_K \end{pmatrix},$$
--   where $I_K$ is the identity and $J_K$ the all-ones $K\times K$ matrix.
--   3. The **covariance of the probit predictions** $\Lambda_{22} = \operatorname{Cov}(\mathbf P) = [(\delta-\rho) I_K + \rho J_K]/(1-\gamma)$ and the two numbers
--   $$\eta_1 = \frac{\delta + (K-1)\rho}{1-\gamma}, \qquad \eta_2 = \frac{\delta-\rho}{1-\gamma}.$$
--   4. The **sufficient statistics** $\bar P = \frac1K \sum_k P_k$ and $S_P = \frac1K\sum_k P_k^2 - \bar P^2$.
--   5. The **likelihood** $\pi(\mathbf P \mid p_0, \theta)$: the density at $\mathbf P$ of the $K$-variate Gaussian distribution with mean $\mathbf 1_K \mu_0/\sqrt{1-\gamma}$ and covariance $\Lambda_{22}$,
--   $$\pi(\mathbf P\mid p_0,\theta) = \frac{1}{\sqrt{(2\pi)^K \det \Lambda_{22}}} \exp\Big\{-\tfrac12 (\mathbf P - m)' \Lambda_{22}^{-1} (\mathbf P - m)\Big\}, \qquad m = \mathbf 1_K \frac{\mu_0}{\sqrt{1-\gamma}}.$$
--   6. The **prior family** of Theorem 3.3, unnormalized,
--   $$\pi(\theta; a, b) = \eta_1^{-(a+1/2)}\, \eta_2^{-(b+1/2)}\, (1-\gamma)^{-(a+5/2)}.$$
--   7. The **Fisher information matrix** $[\mathcal I(\theta)]_{i,j} = \mathbb E\big[\partial_{\theta_i} \log \pi(\mathbf P\mid p_0,\theta)\, \partial_{\theta_j} \log \pi(\mathbf P\mid p_0,\theta)\big]$, the expectation under $\pi(\cdot\mid p_0,\theta)$.
--   8. The sums $S_1 = \sum_k (P_k-\mu_0)^2$ and $S_2 = \sum_{i,k}(P_k-\mu_0)(P_i-\mu_0)$ used in the proof of Theorem 3.3.
--
--   These objects are the shared vocabulary of every statement in the mission. The main result says that likelihood times prior has a finite, positive integral over $\mathcal P(K)$.
--
--   **Formalization Note** The parameter $\theta$ is a function $\mathrm{Fin}\,3 \to \mathbb R$ with $\theta_0=\delta$, $\theta_1=\gamma$, $\theta_2=\rho$. The index `none` of $\Sigma$ is $I_0$ and `some k` is $I_k$. The likelihood is the published `DKFAsymptotics.gaussianPDF` (determinant and matrix inverse); it is *not* defined by the closed form (6), which is Theorem 3.2. Powers with real exponents use `Real.rpow`, the matrix inverse is Mathlib's total inverse, and the Fisher information uses `deriv` and the Bochner integral over Lebesgue measure on $\mathbb R^K$. All of these return junk values (0) at degenerate inputs. Such inputs do not occur on $\mathcal P(K)$ with $K\ge2$, where $0<\gamma<1$, $\delta-\rho>0$ and $\delta+(K-1)\rho>0$, $\Lambda_{22}$ is positive definite, and the Gaussian log-density is smooth with all moments finite. Every theorem of the mission restricts $\theta$ to $\mathcal P(K)$. The common prior $p_0$ is `ProbabilityTheory.cdf (gaussianReal 0 1) μ0`.
-- source:
--   Satopää, Regularized Aggregation of One-off Probability Predictions, SSRN working paper 3769945 (version of 2021-08-10; published in Operations Research 2022), pp. 8–17 and 35–40, §2.2, §3.2, displays (2), (3), (6), Theorems 2.1, 3.2, 3.3, proofs A.2, A.4, A.5

import Mathlib
import Definitions.Def_DKFAsymptotics_Densities

namespace RegAggregation.Posterior

/-- The parameter space `P(K)` of Theorem 2.1 (p. 10), as printed: with `θ = (δ, γ, ρ)`,
`θ 0 = δ`, `θ 1 = γ`, `θ 2 = ρ`, it is `max {0, (Kγ² − γ)/(K − 1)} ≤ ρ < γ ≤ δ`. -/
def PK (K : ℕ) : Set (Fin 3 → ℝ) :=
  {θ | max 0 (((K : ℝ) * θ 1 ^ 2 - θ 1) / ((K : ℝ) - 1)) ≤ θ 2 ∧ θ 2 < θ 1 ∧ θ 1 ≤ θ 0}

/-- The covariance matrix `Σ` of the evidence `(I₀, I₁, …, I_K)` (proof of Theorem 2.1, p. 35):
`Var I₀ = 1`, `Cov(I₀, I_k) = γ`, `Var I_k = γ`, `Cov(I_j, I_k) = ρ` for `j ≠ k`.
The index `none` is `I₀`, the index `some k` is forecaster `k`'s evidence `I_k`. -/
def evidenceCov (K : ℕ) (θ : Fin 3 → ℝ) : Matrix (Option (Fin K)) (Option (Fin K)) ℝ :=
  fun i j =>
    match i, j with
    | none, none => 1
    | none, some _ => θ 1
    | some _, none => θ 1
    | some k, some l => if k = l then θ 1 else θ 2

/-- `Λ₂₂ = Cov(P) = [(δ − ρ) I_K + ρ J_K] / (1 − γ)` (Theorem 3.2, p. 15). -/
noncomputable def Lam (K : ℕ) (θ : Fin 3 → ℝ) : Matrix (Fin K) (Fin K) ℝ :=
  (1 - θ 1)⁻¹ •
    ((θ 0 - θ 2) • (1 : Matrix (Fin K) (Fin K) ℝ) + θ 2 • Matrix.of (fun _ _ => (1 : ℝ)))

/-- `η₁ = [δ + (K − 1)ρ] / (1 − γ)` (Theorem 3.2, p. 15). -/
noncomputable def eta1 (K : ℕ) (θ : Fin 3 → ℝ) : ℝ := (θ 0 + ((K : ℝ) - 1) * θ 2) / (1 - θ 1)

/-- `η₂ = (δ − ρ) / (1 − γ)` (Theorem 3.2, p. 15). -/
noncomputable def eta2 (θ : Fin 3 → ℝ) : ℝ := (θ 0 - θ 2) / (1 - θ 1)

/-- The average `P̄ = (1/K) Σ_k P_k` of the probit predictions (Theorem 3.2, p. 15). -/
noncomputable def Pbar {K : ℕ} (P : Fin K → ℝ) : ℝ := (∑ k, P k) / K

/-- The population variance `S_P = (1/K) Σ_k P_k² − P̄²` (Theorem 3.2, p. 15). -/
noncomputable def SP {K : ℕ} (P : Fin K → ℝ) : ℝ := (∑ k, P k ^ 2) / K - Pbar P ^ 2

/-- The common prior `p₀ = Φ(μ₀)` (p. 9), `Φ` the standard normal distribution function. -/
noncomputable def commonPrior (μ0 : ℝ) : ℝ :=
  ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) μ0

/-- The likelihood `π(P | p₀, θ)` of the probit predictions `P ∈ ℝ^K`: the density of the
`K`-variate Gaussian `N_K(1_K μ₀/√(1 − γ), Λ₂₂)` (p. 14 and proof of Theorem 3.2, p. 37),
written with the determinant and the inverse of `Λ₂₂` through the published
`DKFAsymptotics.gaussianPDF`. -/
noncomputable def lik (K : ℕ) (μ0 : ℝ) (θ : Fin 3 → ℝ) (P : Fin K → ℝ) : ℝ :=
  DKFAsymptotics.gaussianPDF (fun _ => μ0 / Real.sqrt (1 - θ 1)) (Lam K θ) P

/-- The unnormalized prior family of Theorem 3.3 (p. 17):
`π(θ; a, b) ∝ η₁^{−(a+1/2)} η₂^{−(b+1/2)} (1 − γ)^{−(a+5/2)}`. -/
noncomputable def prior (K : ℕ) (a b : ℝ) (θ : Fin 3 → ℝ) : ℝ :=
  eta1 K θ ^ (-(a + 1 / 2)) * eta2 θ ^ (-(b + 1 / 2)) * (1 - θ 1) ^ (-(a + 5 / 2))

/-- The score `∂/∂θ_i log π(x | p₀, θ)` of the likelihood at the data point `x`. -/
noncomputable def score (K : ℕ) (μ0 : ℝ) (θ : Fin 3 → ℝ) (i : Fin 3) (x : Fin K → ℝ) : ℝ :=
  deriv (fun t => Real.log (lik K μ0 (Function.update θ i t) x)) (θ i)

/-- The Fisher information matrix (p. 15):
`[I(θ)]_{i,j} = E[(∂_i log π(P | p₀, θ)) (∂_j log π(P | p₀, θ)) | p₀, θ]`,
the expectation taken under the likelihood `π(· | p₀, θ)` with respect to Lebesgue measure on `ℝ^K`. -/
noncomputable def fisherInfo (K : ℕ) (μ0 : ℝ) (θ : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ∫ x, score K μ0 θ i x * score K μ0 θ j x * lik K μ0 θ x

/-- `S₁ = Σ_k (P_k − μ₀)²` (proof of Theorem 3.3, p. 40). -/
def S1 {K : ℕ} (μ0 : ℝ) (P : Fin K → ℝ) : ℝ := ∑ k, (P k - μ0) ^ 2

/-- `S₂ = Σ_{i,k} (P_k − μ₀)(P_i − μ₀)` (proof of Theorem 3.3, p. 40). -/
def S2 {K : ℕ} (μ0 : ℝ) (P : Fin K → ℝ) : ℝ := ∑ i, ∑ k, (P k - μ0) * (P i - μ0)

end RegAggregation.Posterior


