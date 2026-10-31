-- Prove2me | Definitions.Def_BankLiability_Params
-- name    : BankLiability_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:47:43.743974+00:00
-- url     : https://prove2.me/theorems/d72049b1-6793-4a1f-872b-4af2316353e4
-- title:
--   Exogenous parameters of the bank model (Table 1): $\sigma,\delta,r,\eta,\tau,\alpha,\beta,\omega$
-- statement:
--   The static bank model of Sundaresan and Wang has eight exogenous parameters, listed with their ranges in Table 1:
--
--   1. the asset volatility $\sigma\in(0,\infty)$;
--   2. the asset cash-flow rate $\delta\in[0,\infty)$;
--   3. the risk-free interest rate $r\in(0,\infty)$;
--   4. the deposit profitability $\eta\in(0,r)$, the profit the bank earns from banking services on each dollar of deposits;
--   5. the debt advantage $\tau\in(0,1)$, interpreted as a tax rate: interest and insurance costs $C$ save $\tau C$;
--   6. the liquidation cost $\alpha\in(0,1)$, a fraction of the asset value at liquidation;
--   7. the capital requirement $\beta\in[0,\alpha)$, the minimum ratio of total capital to assets;
--   8. the insurance subsidy $\omega\in[0,1]$, the fraction of the fair deposit-insurance premium that the insurer does not charge.
--
--   A parameter vector of this type always satisfies these ranges. Every other object of the mission is a function of a parameter vector.
--
--   **Formalization Note** The ranges are fields of the structure. The insurance subsidy ranges over Table 1's $[0,1]$; the running text of p.6 writes $0\le\omega<1$, and the structure allows the endpoint $\omega=1$.
-- source:
--   Sundaresan–Wang, Strategic Bank Liability Structure Under Capital Requirements, Management Science (2023), doi:10.1287/mnsc.2022.4570, Articles in Advance, Table 1, p.6 (parameters introduced in §2.1–§2.2, pp.3–6)

import Mathlib

namespace BankLiability

/-- **Exogenous parameters of the bank model, with the ranges of Table 1.**
Sundaresan–Wang, *Strategic Bank Liability Structure Under Capital Requirements*, Management
Science (2023), doi:10.1287/mnsc.2022.4570, Articles in Advance, Table 1, p.6 (and §2.1–§2.2,
pp.3–6, where each parameter is introduced).

* `sigma` = σ ∈ (0, ∞): asset volatility;
* `delta` = δ ∈ [0, ∞): asset cash-flow rate;
* `r` ∈ (0, ∞): risk-free interest rate;
* `eta` = η ∈ (0, r): deposit profitability (profit per dollar of deposits);
* `tau` = τ ∈ (0, 1): debt advantage (tax rate);
* `alpha` = α ∈ (0, 1): liquidation cost as a fraction of the asset value;
* `beta` = β ∈ [0, α): capital requirement (minimum total-capital ratio);
* `omega` = ω ∈ [0, 1]: insurance subsidy as a fraction of the fair premium.

**Formalization Note.** The range of ω is Table 1's `[0,1]`; the running text of p.6 writes
`0 ≤ ω < 1`. The structure allows ω = 1 (the more general of the two). Every parameter vector of
this type satisfies Table 1's ranges: the ranges are fields. -/
structure Params where
  /-- Asset volatility σ. -/
  sigma : ℝ
  /-- Asset cash-flow rate δ. -/
  delta : ℝ
  /-- Risk-free interest rate r. -/
  r : ℝ
  /-- Deposit profitability η. -/
  eta : ℝ
  /-- Debt advantage (tax rate) τ. -/
  tau : ℝ
  /-- Liquidation cost α. -/
  alpha : ℝ
  /-- Capital requirement β. -/
  beta : ℝ
  /-- Insurance subsidy ω. -/
  omega : ℝ
  sigma_pos : 0 < sigma
  delta_nonneg : 0 ≤ delta
  r_pos : 0 < r
  eta_pos : 0 < eta
  eta_lt_r : eta < r
  tau_pos : 0 < tau
  tau_lt_one : tau < 1
  alpha_pos : 0 < alpha
  alpha_lt_one : alpha < 1
  beta_nonneg : 0 ≤ beta
  beta_lt_alpha : beta < alpha
  omega_nonneg : 0 ≤ omega
  omega_le_one : omega ≤ 1

end BankLiability


