-- Prove2me | Definitions.Def_ImpactInvesting_Portfolio_Setting
-- name    : ImpactInvesting_Portfolio_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:01.096552+00:00
-- url     : https://prove2.me/theorems/f31db894-ec31-4066-8f3f-c8fa6d9d3e49
-- title:
--   Assumption (A1), p. 12, with μ_x = 0, σ_x = 1 (pp. 13–14) and μ_α = 0 (p. 13) — IID bivariate normal (X_i, α_i)
-- statement:
--   Let $(\Omega, \mathcal F, P)$ be a probability space and let $X_1,\dots,X_N$ (impact factors) and $\alpha_1,\dots,\alpha_N$ (excess returns) be real random variables. Given $\sigma_\alpha$ and $\rho$, the predicate $\mathrm{A1}(P, X, \alpha, \sigma_\alpha, \rho)$ holds when
--
--   1. each pair $(X_i, \alpha_i)$ has a (bivariate) Gaussian law;
--   2. the pairs $(X_1,\alpha_1), \dots, (X_N,\alpha_N)$ are mutually independent;
--   3. $\mathbb E[X_i] = 0$ and $\operatorname{Var}(X_i) = 1$ for every $i$;
--   4. $\mathbb E[\alpha_i] = 0$ and $\operatorname{Var}(\alpha_i) = \sigma_\alpha^2$ for every $i$;
--   5. $\operatorname{Cov}(X_i, \alpha_i) = \rho\,\sigma_\alpha$ for every $i$, i.e. the correlation of $X_i$ and $\alpha_i$ is $\rho$.
--
--   This is Assumption (A1) of the paper (IID bivariate normal pairs with mean $(\mu_x, \mu_\alpha)$, variances $(\sigma_x^2, \sigma_\alpha^2)$ and correlation $\rho$) together with the normalisations the paper adopts before Proposition 2: $\mu_x = 0$, $\sigma_x = 1$ (pp. 13–14, "without loss of generality") and $\mu_\alpha = 0$ (p. 13, the "auxiliary assumption").
--
--   **Formalization Note.** "Identically distributed" is not a separate clause: a bivariate Gaussian law is determined by its means, variances and covariance, which clauses 3–5 fix to be the same for every $i$. The normalisations are fields of the predicate, not a without-loss-of-generality step. The parameter ranges $\sigma_\alpha > 0$ and $\rho \in (-1,1)$ are hypotheses of the theorems that use the predicate. Gaussianity is Mathlib's `HasGaussianLaw`; moments are the Bochner integral `P[·]`, `Var[·; P]` and `cov[·, ·; P]`.
-- source:
--   Lo & Zhang, Quantifying the Impact of Impact Investing, SSRN 3944367 (draft of 29 June 2023), p. 12, Assumption (A1); p. 13 (μ_α = 0); pp. 13–14 (μ_x = 0, σ_x = 1)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ImpactInvesting.Portfolio

/-- Assumption (A1) of Lo & Zhang (p. 12) with the normalisations μ_x = 0, σ_x = 1 (pp. 13–14) and
μ_α = 0 (p. 13): the pairs `(X i, α i)`, `i : Fin N`, are mutually independent, each pair is bivariate
Gaussian, `X i` has mean 0 and variance 1, `α i` has mean 0 and variance `σα ^ 2`, and the covariance of
`X i` and `α i` is `ρ * σα` (correlation `ρ`). The constraints `0 < σα` and `-1 < ρ < 1` are hypotheses of
the theorems, not fields. -/
structure IsA1 {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω)
    (X α : Fin N → Ω → ℝ) (σα ρ : ℝ) : Prop where
  gaussian : ∀ i, HasGaussianLaw (fun ω => (X i ω, α i ω)) P
  indep : iIndepFun (fun i ω => (X i ω, α i ω)) P
  mean_X : ∀ i, P[X i] = 0
  var_X : ∀ i, Var[X i; P] = 1
  mean_α : ∀ i, P[α i] = 0
  var_α : ∀ i, Var[α i; P] = σα ^ 2
  cov_Xα : ∀ i, cov[X i, α i; P] = ρ * σα

end ImpactInvesting.Portfolio


