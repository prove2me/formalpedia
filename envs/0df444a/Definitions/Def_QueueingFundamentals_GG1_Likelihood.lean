-- Prove2me | Definitions.Def_QueueingFundamentals_GG1_Likelihood
-- name    : QueueingFundamentals_GG1_Likelihood
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T19:34:58.492445+00:00
-- url     : https://prove2.me/theorems/bfd90010-f328-4b04-baa1-bc932cb7c70c
-- title:
--   Clarke's M/M/1 log-likelihood (6.32) without the initial-state term
-- statement:
--   Observe an M/M/1 queue with arrival rate $\lambda$ and service rate $\mu$ for a time $t$. Let $t_b$ be the time the system is busy, $n_a$ the number of arrivals and $n_c$ the number of service completions. Clarke's log-likelihood (6.32) is $-\lambda t-\mu t_b+n_a\ln\lambda+n_c\ln\mu+\ln\Pr\{n_0\}$; when the queue is in equilibrium the initial-state term is ignored, leaving
--
--   $$
--   \mathcal L(\lambda,\mu)=-\lambda t-\mu t_b+n_a\ln\lambda+n_c\ln\mu .
--   $$
--
--   This is the function whose maximizer gives the maximum-likelihood estimators of $\lambda$ and $\mu$.
--
--   **Formalization Note** `Real.log` is `0` at nonpositive arguments; the theorem using this function compares values only at $\lambda,\mu>0$.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.318–319, §6.7, Eq. (6.32) with the ln Pr{n_0} term dropped as on p.319

import Mathlib

namespace QueueingFundamentals.GG1

/-- Clarke's M/M/1 log-likelihood (6.32) (p.319) with the initial-state term `ln Pr{n_0}` dropped,
as the book does for a queue in equilibrium:
`𝓛(λ, μ) = −λt − μt_b + n_a ln λ + n_c ln μ`, where `t` is the observation time, `t_b` the busy
time, `n_a` the number of arrivals and `n_c` the number of service completions (p.318). -/
noncomputable def mm1LogLik (t tb : ℝ) (na nc : ℕ) (lam mu : ℝ) : ℝ :=
  -lam * t - mu * tb + (na : ℝ) * Real.log lam + (nc : ℝ) * Real.log mu

end QueueingFundamentals.GG1


