-- Prove2me | Definitions.Def_BlockchainNV_condExpProfit
-- name    : BlockchainNV_condExpProfit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:41:27.397188+00:00
-- url     : https://prove2.me/theorems/67db3580-ed9a-4440-b703-3e31d3db0042
-- title:
--   Blockchain retailer's expected profit given $X=x$ and order $q$
-- statement:
--   The blockchain retailer observes the freshness state $X = x$ before ordering. Her demand is then $D_x = \lambda + \beta x + \varepsilon$, and her expected profit from ordering $q$ units is
--
--   $$
--   G_x(q) = \mathbb E\big[\,p\min\{q, D_x\} + s\,(q - D_x)^+ - w\,q\,\big],
--   $$
--
--   the expectation being over the demand shock $\varepsilon$. Maximizing $G_x$ over $q$ gives her optimal order quantity (2) and her conditional optimal expected profit $\Pi^*(x)$ (3).
--
--   **Formalization Note** The expectation is the integral over the probability space $(\Omega, P)$ carrying $\varepsilon$; $x$ and $q$ are arbitrary reals.
-- source:
--   Keskin, Li, Song, The Blockchain Newsvendor: Value of Freshness Transparency and Smart Contracts, Management Science (2024), doi:10.1287/mnsc.2021.02949, §2.1, p.8 (PDF p.8)

import Mathlib
import Definitions.Def_BlockchainNV_profit
import Definitions.Def_BlockchainNV_Params

open MeasureTheory

namespace BlockchainNV

/-- Keskin, Li, Song, *The Blockchain Newsvendor*, Management Science (2024),
doi:10.1287/mnsc.2021.02949, §2.1, p.8 (PDF p.8): the blockchain retailer's expected profit
when she has observed the freshness state `X = x` and orders `q`. Her demand is then
`D_x = λ + βx + ε`, and the expectation is over the demand shock `ε`:
`E[p min{q, D_x} + s (q − D_x)⁺ − w q]`.

**Formalization Note.** The expectation is the Bochner integral over the probability space
`(Ω, P)` carrying `ε`; `q` and `x` range over all of `ℝ`. -/
noncomputable def condExpProfit (θ : Params) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ε : Ω → ℝ) (x q : ℝ) : ℝ :=
  ∫ ω, profit θ.p θ.w θ.s q (θ.lam + θ.beta * x + ε ω) ∂P

end BlockchainNV


