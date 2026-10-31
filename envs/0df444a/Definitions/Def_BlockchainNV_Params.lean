-- Prove2me | Definitions.Def_BlockchainNV_Params
-- name    : BlockchainNV_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:40:40.078376+00:00
-- url     : https://prove2.me/theorems/7c7a0cae-469a-4ce6-8247-92455eee7ec1
-- title:
--   Parameters and standing assumptions of the blockchain newsvendor base model
-- statement:
--   The base model has eight real parameters:
--
--   1. the unit retail price $p$, the unit wholesale price $w$ and the unit salvage value $s$, with $w > 0$, $p > w$ and $s < w$ (the salvage value may be zero or negative, a disposal cost);
--   2. the baseline demand level $\lambda > 0$ and the freshness sensitivity of demand $\beta > 0$;
--   3. the mean $\mu_X$ and standard deviation $\sigma_X > 0$ of the freshness state $X \sim N(\mu_X, \sigma_X^2)$;
--   4. the standard deviation $\sigma > 0$ of the demand shock $\varepsilon \sim N(0, \sigma^2)$.
--
--   Demand is $D = \lambda + \beta X + \varepsilon$ (eq. (1)). The structure bundles the eight numbers with exactly these standing inequalities.
--
--   **Formalization Note** $\lambda, \beta, \mu_X$ are named `lam`, `beta`, `muX`. The paper does not print $\sigma_X > 0$ and $\sigma > 0$; they are the reading under which its formulas are defined (it divides by $\sigma$ in Lemma EC.1 and by $\sigma_X$ on p.13).
-- source:
--   Keskin, Li, Song, The Blockchain Newsvendor: Value of Freshness Transparency and Smart Contracts, Management Science (2024), doi:10.1287/mnsc.2021.02949, §2, p.7 (PDF p.7)

import Mathlib

namespace BlockchainNV

/-- Keskin, Li, Song, *The Blockchain Newsvendor*, Management Science (2024),
doi:10.1287/mnsc.2021.02949, §2, p.7 (PDF p.7): the parameters of the base model and its standing
assumptions. Unit wholesale price `w > 0`, unit retail price `p > w`, unit salvage value `s < w`
(`s` may be zero or negative); baseline demand level `λ > 0` (`lam`), freshness sensitivity
`β > 0` (`beta`); the freshness state is `X ∼ N(µ_X, σ_X²)` (`muX`, `sigmaX`) and the demand shock
is `ε ∼ N(0, σ²)` (`sigma`), so demand (1) is `D = λ + βX + ε`.

**Formalization Note.** `sigmaX` and `sigma` are standard deviations with `σ_X > 0` and `σ > 0`.
The page does not print these two inequalities; they are the reading under which the paper's
formulas are defined (it divides by `σ` in Lemma EC.1 and by `σ_X` on p.13), and with `σ_X = 0`
the value of transparency in Theorem 1 would be `0`. -/
structure Params where
  /-- unit retail price `p` -/
  p : ℝ
  /-- unit wholesale price `w` -/
  w : ℝ
  /-- unit salvage value `s` -/
  s : ℝ
  /-- baseline demand level `λ` -/
  lam : ℝ
  /-- freshness sensitivity of demand `β` -/
  beta : ℝ
  /-- mean freshness `µ_X` -/
  muX : ℝ
  /-- standard deviation of the freshness state `σ_X` -/
  sigmaX : ℝ
  /-- standard deviation of the demand shock `σ` -/
  sigma : ℝ
  w_pos : 0 < w
  w_lt_p : w < p
  s_lt_w : s < w
  lam_pos : 0 < lam
  beta_pos : 0 < beta
  sigmaX_pos : 0 < sigmaX
  sigma_pos : 0 < sigma

end BlockchainNV


