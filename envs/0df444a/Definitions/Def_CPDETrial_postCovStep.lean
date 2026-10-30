-- Prove2me | Definitions.Def_CPDETrial_postCovStep
-- name    : CPDETrial_postCovStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:45:44.083752+00:00
-- url     : https://prove2.me/theorems/a54e825a-b769-4280-a757-7c917d1a525c
-- title:
--   One-observation posterior covariance update (eq. (8), $\tau=1$)
-- statement:
--   Let $\Sigma$ be the current covariance matrix of the belief about the arm means $\theta\in\mathbb R^M$, and let $\lambda_i>0$ be the sampling variance of arm $i$. After one observation of arm $i$, Bayes' rule gives the covariance
--
--   $$
--   \Sigma' = \Sigma - \frac{\Sigma e_i e_i^{\top}\Sigma}{\lambda_i + \Sigma_{i,i}},\qquad \Sigma'_{a,b} = \Sigma_{a,b} - \frac{\Sigma_{a,i}\Sigma_{i,b}}{\lambda_i+\Sigma_{i,i}},
--   $$
--
--   where $e_i$ is the $i$-th unit vector. This is eq. (8) of the paper with $\tau = 1$; iterating it along the allocations of a trial gives the posterior covariances $\Sigma^t$.
--
--   **Formalization Note** The denominator $\lambda_i+\Sigma_{i,i}$ is positive whenever the formula is used ($\lambda_i>0$, $\Sigma_{i,i}\ge 0$).
-- source:
--   Chick, Gans & Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN preprint 3184758 (version of August 31, 2020), p. 9, eq. (8) with τ = 1

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CPDETrial

/-- **One-observation posterior covariance update, eq. (8) with `τ = 1`.**
Chick, Gans & Yapar, *Bayesian Sequential Learning for Clinical Trials of Multiple Correlated
Medical Interventions*, SSRN preprint 3184758 (version of August 31, 2020), §3.1, eq. (8), p. 9: "`Σ^{t+τ} = Σ^t − Σ^t e_i e_iᵀ Σ^t / (λ_i/τ + Σ^t_{i,i})`".

`postCovStep lam S i` is the covariance `Σ^{t+1}` of the arm means after one observation of arm
`i`, when the current covariance is `S = Σ^t` and the sampling variances are `lam = (λ_1,…,λ_M)`:
`S − (λ_i + S_ii)⁻¹ · (S e_i)(e_iᵀ S)`, whose `(a, b)` entry is `S a b − S a i * S i b / (λ_i + S_ii)`.

**Formalization Note.** Lean's `1 / 0 = 0`: the formula is only used with `λ_i > 0` and
`S_ii ≥ 0` (Λ and `Σ⁰` positive definite, Assumption 1(ii)), where the denominator is positive. -/
noncomputable def postCovStep {M : ℕ} (lam : Fin M → ℝ≥0) (S : Matrix (Fin M) (Fin M) ℝ)
    (i : Fin M) : Matrix (Fin M) (Fin M) ℝ :=
  S - (1 / ((lam i : ℝ) + S i i)) • Matrix.of (fun a b => S a i * S i b)

end CPDETrial


