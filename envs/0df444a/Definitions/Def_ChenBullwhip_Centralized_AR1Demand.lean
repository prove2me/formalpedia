-- Prove2me | Definitions.Def_ChenBullwhip_Centralized_AR1Demand
-- name    : ChenBullwhip_Centralized_AR1Demand
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:59:51.762987+00:00
-- url     : https://prove2.me/theorems/7bf58c56-c5a0-4f65-9f35-3f990f72fafe
-- title:
--   Steady-state AR(1) demand with i.i.d. symmetric errors, Eq. (1)
-- statement:
--   Let $(\Omega, \mathcal F, P)$ be a probability space and index time by the integers $t \in \mathbb Z$. An **AR(1) demand process** in the sense of Chen, Drezner, Ryan and Simchi-Levi consists of real parameters $\mu$, $\rho$, $\sigma$ and two families of real random variables, the errors $(\epsilon_t)_{t\in\mathbb Z}$ and the customer demands $(D_t)_{t \in \mathbb Z}$, such that
--
--   $$D_t = \mu + \rho D_{t-1} + \epsilon_t \qquad \text{for every } t \in \mathbb Z \text{ and every outcome } \omega, \tag{1}$$
--
--   and:
--
--   1. $\mu \ge 0$, $|\rho| < 1$ and $\sigma > 0$;
--   2. the errors $\epsilon_t$ are mutually independent and identically distributed;
--   3. the error distribution is symmetric: $\epsilon_t$ and $-\epsilon_t$ have the same law;
--   4. each $\epsilon_t$ is square integrable, with mean $0$ and variance $\sigma^2$;
--   5. the demand is in **steady state**: every $D_t$ is square integrable and all $D_t$ have the same law as $D_0$.
--
--   The paper asserts that $E(D_t) = \mu/(1-\rho)$ and $\mathrm{Var}(D_t) = \sigma^2/(1-\rho^2)$; these are the moments of the stationary solution of (1), which condition 5 selects. With i.i.d. square-integrable errors and $|\rho|<1$, the stationary solution is, almost surely, $D_t = \mu/(1-\rho) + \sum_{j \ge 0} \rho^j \epsilon_{t-j}$; this also shows that each error $\epsilon_t$ is independent of the past demands. Nothing beyond symmetry, mean and variance is assumed about the error law.
--
--   This structure carries every later statement of the mission: the moving-average estimators, the retailer's orders and the orders of a multistage chain are all functions of these demands.
--
--   **Formalization Note** Three conditions are added to the page and disclosed: $\sigma > 0$ (the paper's results divide by $\mathrm{Var}(D) = \sigma^2/(1-\rho^2)$); square integrability of the errors and demands (the paper takes their variances, and Mathlib's variance of a non-square-integrable function is $0$); and the steady-state condition 5. Measurability of $\epsilon_t$ follows from (1) and the measurability of the demands. The published Gaussian structure `SupplyChainTheory.AR1Demand` (Snyder and Shen, Eq. (13.1), with errors $N(0,\sigma^2)$ and Gaussian stationary marginals) satisfies all these conditions, so it is a special case of this one.
-- source:
--   Chen, Drezner, Ryan and Simchi-Levi, Quantifying the Bullwhip Effect in a Simple Supply Chain, Management Science 46 (2000), p. 437, Eq. (1) and the sentence following it

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ChenBullwhip.Centralized

/-- Chen–Drezner–Ryan–Simchi-Levi (2000), p. 437, Eq. (1): the steady-state AR(1) demand
`D t = μ + ρ D (t - 1) + ε t` on the integer time line, with `μ ≥ 0`, `|ρ| < 1` and errors
`ε t` i.i.d. from a symmetric distribution with mean `0` and variance `σ²`.

Added relative to the page (disclosed): `σ > 0` (the paper divides by `Var(D)`), the errors and
demands are square integrable (the paper takes their variances), and the demand is in steady state:
every `D t` is square integrable and has the law of `D 0` (the paper's "it can easily be shown that
`E(D_t) = μ/(1-ρ)` and `Var(D_t) = σ²/(1-ρ²)`" presupposes the stationary solution of (1)). -/
structure AR1Demand {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] where
  /-- The constant `μ` of Eq. (1). -/
  mu : ℝ
  /-- The correlation parameter `ρ`. -/
  rho : ℝ
  /-- The error standard deviation `σ`. -/
  sigma : ℝ
  mu_nonneg : 0 ≤ mu
  abs_rho_lt_one : |rho| < 1
  sigma_pos : 0 < sigma
  /-- The error terms `ε t`. -/
  eps : ℤ → Ω → ℝ
  /-- The customer demands `D t` seen by the retailer. -/
  D : ℤ → Ω → ℝ
  measurable_D : ∀ t, Measurable (D t)
  /-- The errors are mutually independent ... -/
  eps_iIndep : iIndepFun eps P
  /-- ... and identically distributed. -/
  eps_identDistrib : ∀ t, IdentDistrib (eps t) (eps 0) P P
  /-- The error distribution is symmetric: `ε t` and `-ε t` have the same law. -/
  eps_symm : ∀ t, IdentDistrib (eps t) (fun ω => -eps t ω) P P
  eps_memLp : ∀ t, MemLp (eps t) 2 P
  eps_mean : ∀ t, ∫ ω, eps t ω ∂P = 0
  eps_variance : ∀ t, variance (eps t) P = sigma ^ 2
  /-- Eq. (1), for every outcome. -/
  recursion : ∀ t : ℤ, ∀ ω, D t ω = mu + rho * D (t - 1) ω + eps t ω
  /-- Steady state: the demands are square integrable ... -/
  D_memLp : ∀ t, MemLp (D t) 2 P
  /-- ... and all have the same law. -/
  stationary : ∀ t, IdentDistrib (D t) (D 0) P P

end ChenBullwhip.Centralized


