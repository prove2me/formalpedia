-- Prove2me | Definitions.Def_InvMarketMaking_LOB_IsValuationLaw
-- name    : InvMarketMaking_LOB_IsValuationLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:18:42.877227+00:00
-- url     : https://prove2.me/theorems/7272b060-2801-48db-8284-b00dde341d33
-- title:
--   Standing assumptions on the valuation law $\mathcal V$ (support in $[0,1]^2$, $\mathbb P(V^{\mathrm{buy}}=1)=\mathbb P(V^{\mathrm{sell}}=0)=0$)
-- statement:
--   In each round of the maker–takers interaction a seller and a buyer arrive with private valuations $(V^{\mathrm{sell}}_t, V^{\mathrm{buy}}_t)$, drawn from an unknown joint law $\mathcal V$ on pairs; the first coordinate is the seller's valuation and the second the buyer's. The **standing assumptions** on $\mathcal V$ are
--
--   1. $\mathcal V$ is supported in $[0,1]^2$, i.e. $\mathcal V\big(([0,1]\times[0,1])^{\mathrm c}\big)=0$;
--   2. $\mathbb P(V^{\mathrm{buy}}=1)=0$;
--   3. $\mathbb P(V^{\mathrm{sell}}=0)=0$.
--
--   The two valuations of a round may be arbitrarily correlated. Assumptions 2–3 say that bidding $0$ or asking $1$ never trades, so these prices act as "do nothing"; equivalently $F(0)=0$ and $S(1)=0$ for the functions $F,S$ of the surrogate objective.
--
--   **Formalization Note** $\mathcal V$ is a measure on $\mathbb R\times\mathbb R$; the theorems that use this predicate also assume it is a probability measure.
-- source:
--   Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Sec. 3, p. 14

import Mathlib

namespace InvMarketMaking.LOB

open MeasureTheory

/-- The standing assumptions on the joint valuation law `V` of a round (Maran, Restelli, Stradi,
No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints,
arXiv:2610.24562v1, Sec. 3, p. 14): `V` is a law on pairs `(V^sell, V^buy)` (first coordinate the
seller's valuation, second the buyer's) supported in `[0,1]²`, and
`P(V^buy = 1) = P(V^sell = 0) = 0`.

**Formalization Note** `V` is a measure on `ℝ × ℝ`; the theorems that use this predicate also
assume `[IsProbabilityMeasure V]`. "Supported in `[0,1]²`" is `V(([0,1] × [0,1])ᶜ) = 0`. The two
coordinates may be arbitrarily correlated within a round; no independence, continuity or density
is assumed. -/
def IsValuationLaw (V : Measure (ℝ × ℝ)) : Prop :=
  V (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧ V {p | p.2 = 1} = 0 ∧ V {p | p.1 = 0} = 0

end InvMarketMaking.LOB


