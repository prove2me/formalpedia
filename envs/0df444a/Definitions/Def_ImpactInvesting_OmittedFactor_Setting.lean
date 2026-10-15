-- Prove2me | Definitions.Def_ImpactInvesting_OmittedFactor_Setting
-- name    : ImpactInvesting_OmittedFactor_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:35.969316+00:00
-- url     : https://prove2.me/theorems/8add66cb-c744-447f-97cf-ba9321ab265b
-- title:
--   Assumption (A2), (22)–(24), pp. 19, 67 — jointly Gaussian impact factors X and omitted-factor returns λ, and the adjusted correlation ρ_adj
-- statement:
--   Fix $N$ securities. For security $i$, $X_i$ is its observable **impact factor** and $\lambda_i$ the total contribution of the omitted asset-pricing factors to its return. Let $X = (X_1,\dots,X_N)$ and $\lambda = (\lambda_1,\dots,\lambda_N)$ be random vectors on a probability space $(\Omega, \mathcal F, P)$, and let $\mu_\lambda, \sigma_\lambda, \rho_{x,\lambda}, \rho_x, \rho_\lambda, \tilde\rho_{x,\lambda}$ be real parameters.
--
--   **Assumption (A2)**, normalised as in the paper ($\mu_x = 0$, $\sigma_x = 1$), says:
--
--   1. the $2N$-vector $(X, \lambda)$ is jointly Gaussian;
--   2. for every $i$: $\mathbb E[X_i] = 0$, $\mathrm{Var}(X_i) = 1$, $\mathbb E[\lambda_i] = \mu_\lambda$, $\mathrm{Var}(\lambda_i) = \sigma_\lambda^2$ and $\mathrm{Cov}(X_i, \lambda_i) = \rho_{x,\lambda}\sigma_\lambda$ (display (22));
--   3. for every $i \ne j$: $\mathrm{Cov}(X_i, X_j) = \rho_x$, $\mathrm{Cov}(\lambda_i, \lambda_j) = \rho_\lambda\sigma_\lambda^2$ and $\mathrm{Cov}(X_i, \lambda_j) = \tilde\rho_{x,\lambda}\sigma_\lambda$ (display (23)).
--
--   With $\sigma_x = 1$ and $\sigma_\lambda > 0$ these covariances say exactly that the correlations are $\rho_{x,\lambda}$, $\rho_x$, $\rho_\lambda$, $\tilde\rho_{x,\lambda}$ as in (22)–(23).
--
--   The **adjusted correlation** of display (24) is
--   $$\rho_{adj} = \frac{\rho_{x,\lambda} - \tilde\rho_{x,\lambda}}{1 - \rho_x}.$$
--
--   This is the model of Section 4.3, in which the apparent alphas of impact-ranked securities are risk premia of factors the investor omits; Proposition 5 computes the first two moments of $\lambda_{[i:N]}$ in it.
--
--   **Formalization Note** (A2) as printed asks only that each pair $(X_i, \lambda_i)$ be bivariate normal; the paper's proof (A.40) treats $(X, \lambda)$ as one Gaussian vector whose specification "completely characterizes the joint distribution of X and λ". The joint reading is the one formalized, and it is necessary: pairwise normality does not make the residual of the regression of $\lambda$ on $X$ independent of $X$. The normalisations $\mu_x = 0$, $\sigma_x = 1$ ("without loss of generality", p. 19) are fields of the predicate; $\mu_\lambda$ is left free, as in the paper. Correlations are stated as covariances. `lam` stands for $\lambda$ (a Lean keyword), `ρxlamt` for $\tilde\rho_{x,\lambda}$. The definition `rhoAdj` uses Lean's division, which returns $0$ at $\rho_x = 1$; every theorem assumes $\rho_x < 1$.
-- source:
--   Lo & Zhang, Quantifying the Impact of Impact Investing, SSRN 3944367 (draft of 29 June 2023), p. 19, Assumption (A2), (22), (23), normalisation μx = 0, σx = 1, Proposition 5 (24); p. 67, Appendix B.5, (A.40)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ImpactInvesting.OmittedFactor

/-- Assumption (A2) of Lo & Zhang (p. 19), read as in (A.40) (p. 67): the 2N-vector (X, λ) is jointly
Gaussian with the exchangeable moments (22)–(23), normalised μ_x = 0, σ_x = 1 (p. 19). `lam` stands for
λ, `μlam` for μ_λ, `σlam` for σ_λ, `ρxlam` for ρ_{x,λ}, `ρx` for ρ_x, `ρlam` for ρ_λ and `ρxlamt` for
ρ̃_{x,λ}. Correlations are stated as covariances: with σ_x = 1, Corr(X_i, λ_j) = ρ means
Cov(X_i, λ_j) = ρ σ_λ, and Corr(λ_i, λ_j) = ρ_λ means Cov(λ_i, λ_j) = ρ_λ σ_λ². -/
structure IsA2 {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω)
    (X lam : Fin N → Ω → ℝ) (μlam σlam ρxlam ρx ρlam ρxlamt : ℝ) : Prop where
  gaussian : HasGaussianLaw (fun ω => ((fun i => X i ω), (fun i => lam i ω))) P
  mean_X : ∀ i, P[X i] = 0
  var_X : ∀ i, Var[X i; P] = 1
  mean_lam : ∀ i, P[lam i] = μlam
  var_lam : ∀ i, Var[lam i; P] = σlam ^ 2
  cov_X_lam : ∀ i, cov[X i, lam i; P] = ρxlam * σlam
  cov_X_X : ∀ i j, i ≠ j → cov[X i, X j; P] = ρx
  cov_lam_lam : ∀ i j, i ≠ j → cov[lam i, lam j; P] = ρlam * σlam ^ 2
  cov_X_lam_cross : ∀ i j, i ≠ j → cov[X i, lam j; P] = ρxlamt * σlam

/-- The adjusted correlation (24) of Proposition 5 (p. 19): ρ_adj = (ρ_{x,λ} − ρ̃_{x,λ}) / (1 − ρ_x). -/
noncomputable def rhoAdj (ρxlam ρx ρxlamt : ℝ) : ℝ := (ρxlam - ρxlamt) / (1 - ρx)

end ImpactInvesting.OmittedFactor


