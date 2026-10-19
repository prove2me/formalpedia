-- Prove2me | Definitions.Def_CorrelatedTrials_Consistency_Model
-- name    : CorrelatedTrials_Consistency_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:36.390722+00:00
-- url     : https://prove2.me/theorems/0562acc1-8c16-4daa-b98a-ca858ff49749
-- title:
--   §1.1–1.2, (8), Assumption 1 — trial instance and the Bayesian update for one observation
-- statement:
--   A clinical trial compares $M\ge 2$ interventions (arms), indexed $i\in\{0,\dots,M-1\}$. Arm $i$ has an unknown mean benefit $\theta_i$, and each observation $Y$ of arm $i$ satisfies $Y\mid\theta_i\sim N(\theta_i,\lambda_i)$ with a known sampling variance $\lambda_i>0$. The mean vector has a correlated Gaussian prior $\theta\sim N(\mu^0,\Sigma^0)$ with $\Sigma^0$ positive definite, and sampling arm $i$ costs $c_i>0$.
--
--   An **instance** collects $(\mu^0,\Sigma^0,\lambda,c)$ together with these four conditions: $M\ge2$, $\Sigma^0$ positive definite, $\lambda_i>0$ and $c_i>0$ for every $i$.
--
--   The **Bayesian update** after one observation $y$ of arm $i$, starting from the belief $(\mu,\Sigma)$, is equation (8) with $\tau=1$:
--
--   $$
--   \mu' = \mu + \frac{y-\mu_i}{\lambda_i+\Sigma_{i,i}}\,\Sigma e_i,
--   \qquad
--   \Sigma' = \Sigma - \frac{\Sigma e_i e_i^{\top}\Sigma}{\lambda_i+\Sigma_{i,i}},
--   $$
--
--   where $e_i$ is the $i$-th unit vector, so that $\Sigma e_i$ is the $i$-th column of $\Sigma$ and $(\Sigma e_ie_i^\top\Sigma)_{j,k}=\Sigma_{j,i}\Sigma_{i,k}$.
--
--   These objects are the model on which the cPDE allocation policy and its consistency theorem are built.
--
--   **Formalization Note** The four conditions are §1.1's $M\ge2$ and Assumption 1 ii) and iv) of p. 13. Assumption 1 i) is the model itself; Assumption 1 iii) concerns consideration sets $\mathcal M_t$, and the cPDE policy considers every arm at every time ($\mathcal M_t=\mathcal M$), so it holds trivially and is not a field. The undiscounted case $\Delta=1$ is built into the index (EC.8). Arms are 0-based: the paper's arm 1 is index $0$.
-- source:
--   Chick, Gans, Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN 3184758 (version of August 31, 2020), pp. 5–6, §1.1–1.2; p. 9, (8); p. 13, Assumption 1

import Mathlib

namespace CorrelatedTrials.Consistency

/-- A trial instance (Chick, Gans, Yapar, Bayesian Sequential Learning for Clinical Trials of
Multiple Correlated Medical Interventions, SSRN 3184758 (version of August 31, 2020), pp. 5–6,
§1.1–1.2, and p. 13, Assumption 1 ii), iv)).

`M` arms, indexed by `Fin M` (the paper's arm `1` is `0`); the prior mean `mu0` and prior
covariance `Sig0` of the unknown mean vector `θ ∼ N(µ0, Σ0)`; the known sampling variances
`lam i = λ_i` of the observations `Y | θ_i ∼ N(θ_i, λ_i)`; and the sampling costs `c i = c_i`.

Formalization Note: the fields are §1.1's `M ≥ 2` and Assumption 1 ii) (`Σ0` and `Λ = diag(λ)`
positive definite) and iv) (`c_j > 0`; `∆ = 1` is built into the index (EC.8), which carries no
discount). Assumption 1 i) is the model itself. Assumption 1 iii) concerns the consideration sets
`M_t`; the cPDE policy maximizes over all arms (`M_t = M`), so iii) holds trivially and is
dropped. -/
structure Instance (M : ℕ) where
  /-- prior mean `µ0` -/
  mu0 : Fin M → ℝ
  /-- prior covariance `Σ0` -/
  Sig0 : Matrix (Fin M) (Fin M) ℝ
  /-- sampling variances `λ_i` -/
  lam : Fin M → ℝ
  /-- sampling costs `c_i` -/
  c : Fin M → ℝ
  two_le : 2 ≤ M
  posDef : Sig0.PosDef
  lam_pos : ∀ i, 0 < lam i
  c_pos : ∀ i, 0 < c i

/-- The Bayesian update (8) (p. 9) after one observation `y` of arm `i` (`τ = 1`):
`µ' = µ + (y − µ_i)/(λ_i + Σ_{i,i}) · Σ e_i` and
`Σ' = Σ − Σ e_i e_iᵀ Σ / (λ_i + Σ_{i,i})`.

Formalization Note: `Σ e_i` is the `i`-th column `fun j => Sig j i`, and `Σ e_i e_iᵀ Σ` is the
matrix with entries `Sig j i * Sig i k`. -/
noncomputable def update {M : ℕ} (lam : Fin M → ℝ) (mu : Fin M → ℝ)
    (Sig : Matrix (Fin M) (Fin M) ℝ) (i : Fin M) (y : ℝ) :
    (Fin M → ℝ) × Matrix (Fin M) (Fin M) ℝ :=
  (fun j => mu j + (y - mu i) / (lam i + Sig i i) * Sig j i,
   Matrix.of fun j k => Sig j k - Sig j i * Sig i k / (lam i + Sig i i))

end CorrelatedTrials.Consistency


