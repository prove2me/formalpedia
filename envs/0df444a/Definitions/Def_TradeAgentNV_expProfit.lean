-- Prove2me | Definitions.Def_TradeAgentNV_expProfit
-- name    : TradeAgentNV_expProfit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:30:19.477989+00:00
-- url     : https://prove2.me/theorems/ecbff7d0-0ba6-4cc8-9e2e-041b6af9c5b1
-- title:
--   Expected profit $E[V^y(b)]$ of the trade agent
-- statement:
--   Let $Z$ (ask price) and $U$ (yield fraction) be random variables on $(\Omega,\mathcal F,P)$. At bid $b$ the agent wins when $Z\le b$ and then earns the won-bid profit at the realized yield $U$; otherwise it procures nothing and loses all demand at cost $\pi D$. The **expected profit** is
--   $$
--   E[V^y(b)]=E\Big[\mathbf 1\{Z\le b\}\big((r-t)\min(qU,D)-bq-h(qU-D)^+-\pi(D-qU)^+\big)-\mathbf 1\{Z>b\}\,\pi D\Big].
--   $$
--   This is the primitive model of displays (2)–(3); the agent's problem is to maximize it over bids $b\in\Omega=[0,\infty)$.
--
--   **Formalization Note** The expectation is the Lebesgue (Bochner) integral over $P$; the theorems that use it assume $Z,U$ measurable and $0\le U\le1$ a.s., so the integrand is bounded and integrable.
-- source:
--   Çakıcı & Karaesmen, When Yield is Not the Only Supply Uncertainty: Newsvendor Model of a Trade Agent, SSRN 4409114 (v. Oct 14, 2023), https://ssrn.com/abstract=4409114, §3.1–3.2, displays (2)–(3), pp.9–10

import Mathlib
import Definitions.Def_TradeAgentNV_wonProfit

open MeasureTheory

namespace TradeAgentNV

/-- The trade agent's **expected profit** `E[Vʸ(b)]` at bid `b` (displays (2)–(3), pp.9–10,
of Çakıcı & Karaesmen, *When Yield is Not the Only Supply Uncertainty: Newsvendor Model of a
Trade Agent*, SSRN 4409114 (v. Oct 14, 2023)). On the probability space `(Ω, P)` the seller's ask price is
`Z` and the yield fraction is `U`. The bid wins when `Z ≤ b` (display (1)); then the agent
earns the won-bid profit `wonProfit r t h π D q b (U ω)` at the realized yield. Otherwise it gets
nothing and loses all the demand, at cost `πD`. The expected profit is the expectation of this
profit under `P`.

**Formalization Note.** This is the primitive model of (2)–(3): the win event and the yield are
both random variables on one space, and the expectation is the Bochner integral. The h/π
assignment is that of p.8 and display (4) (see `wonProfit`). -/
noncomputable def expProfit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z U : Ω → ℝ)
    (r t h π D q b : ℝ) : ℝ :=
  ∫ ω, (if Z ω ≤ b then wonProfit r t h π D q b (U ω) else -(π * D)) ∂P

end TradeAgentNV


