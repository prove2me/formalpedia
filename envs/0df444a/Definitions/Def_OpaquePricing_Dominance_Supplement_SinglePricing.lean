-- Prove2me | Definitions.Def_OpaquePricing_Dominance_Supplement_SinglePricing
-- name    : OpaquePricing_Dominance_Supplement_SinglePricing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:29:48.010424+00:00
-- url     : https://prove2.me/theorems/9fac9c69-d460-4712-9e4e-3a4b3500e33f
-- title:
--   Single pricing: expected tail revenue and optimal revenue
-- statement:
--   Let $N$ be the number of items, $v\in\mathbb R^N$ a valuation profile, and $\mu$ its law. Single pricing offers all items at a common price $p\ge0$. Write $M(v)=\max_i v_i$. Its expected and optimal revenues are
--   $$R_{SP}(\mu,p)=p\,\mu\{v:\exists i,\ v_i\ge p\},\qquad R_{SP}(\mu)=\sup_{p\ge0}R_{SP}(\mu,p).$$
--   These quantities supply the common benchmark for the companion theorems. Expectations and suprema take values in $[0,\infty]$, allowing arbitrary tails. The helper maximum is the published first order statistic; it returns zero on the unused $N=0$ case. A separate, proved local verification identifies the tail formula with the published constant-price DP choice revenue.
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), §2.2, pp. 10–11

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting

open MeasureTheory

namespace OpaquePricing.Dominance.Supplement

/-- The maximum valuation, with a harmless zero value for the unused empty-item case. -/
noncomputable def maxValue {N : ℕ} (v : Fin N → ℝ) : ℝ := orderStat v 0

/-- The tail formula from §2.2; the existential event also handles atoms exactly. -/
noncomputable def expSP {N : ℕ} (μ : Measure (Fin N → ℝ)) (p : ℝ) : ENNReal :=
  ENNReal.ofReal p * μ {v | ∃ i, p ≤ v i}

noncomputable def optSP {N : ℕ} (μ : Measure (Fin N → ℝ)) : ENNReal :=
  ⨆ (p : ℝ) (_ : 0 ≤ p), expSP μ p

end OpaquePricing.Dominance.Supplement


