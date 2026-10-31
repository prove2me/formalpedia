-- Prove2me | Definitions.Def_BlockchainNV_tradExpProfit
-- name    : BlockchainNV_tradExpProfit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:41:16.82757+00:00
-- url     : https://prove2.me/theorems/4fdebdec-ecf5-442f-8f56-2cab21280f3b
-- title:
--   Traditional retailer's expected profit for order $q$
-- statement:
--   The traditional retailer knows only the distribution of the freshness state $X$, so she faces the compound demand $D = \lambda + \beta X + \varepsilon$ of (1). Her expected profit from ordering $q$ units is
--
--   $$
--   G(q) = \mathbb E\big[\,p\min\{q, D\} + s\,(q - D)^+ - w\,q\,\big].
--   $$
--
--   Maximizing $G$ over $q$ gives her optimal order quantity (4) and her optimal expected profit $\Pi^*_o$.
--
--   **Formalization Note** The expectation is the integral over the probability space $(\Omega, P)$ carrying $X$ and $\varepsilon$; $q$ is an arbitrary real.
-- source:
--   Keskin, Li, Song, The Blockchain Newsvendor: Value of Freshness Transparency and Smart Contracts, Management Science (2024), doi:10.1287/mnsc.2021.02949, §2.1, p.8 (PDF p.8)

import Mathlib
import Definitions.Def_BlockchainNV_profit
import Definitions.Def_BlockchainNV_Params

open MeasureTheory

namespace BlockchainNV

/-- Keskin, Li, Song, *The Blockchain Newsvendor*, Management Science (2024),
doi:10.1287/mnsc.2021.02949, §2.1, p.8 (PDF p.8): the traditional retailer's expected profit
when she orders `q` without observing the freshness state, i.e. against the compound demand
`D = λ + βX + ε` of (1): `E[p min{q, D} + s (q − D)⁺ − w q]`.

**Formalization Note.** The expectation is the Bochner integral over the probability space
`(Ω, P)` carrying `X` and `ε`; `q` ranges over all of `ℝ`. -/
noncomputable def tradExpProfit (θ : Params) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X ε : Ω → ℝ) (q : ℝ) : ℝ :=
  ∫ ω, profit θ.p θ.w θ.s q (θ.lam + θ.beta * X ω + ε ω) ∂P

end BlockchainNV


