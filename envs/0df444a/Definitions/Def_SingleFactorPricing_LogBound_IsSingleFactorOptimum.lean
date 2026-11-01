-- Prove2me | Definitions.Def_SingleFactorPricing_LogBound_IsSingleFactorOptimum
-- name    : SingleFactorPricing_LogBound_IsSingleFactorOptimum
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:16:57.618434+00:00
-- url     : https://prove2.me/theorems/22bb1c89-ebc5-451f-8655-97da10d1ff5d
-- title:
--   The single-factor profit $\mathcal R^f$
-- statement:
--   A real number $\mathcal R^f$ is the **single-factor profit** of the direction $f$ when
--
--   $$
--   \mathcal R^f=\sup_{q>0}R(qf).
--   $$
--
--   The paper writes $\mathcal R^f:=\max_{q>0}R(qf)$. The choice $f=e$, the vector of ones, gives the optimal profit $\mathcal R^e$ under uniform pricing.
--
--   **Formalization Note** This is `IsLUB` of the set of values, not a real `⨆`, which would be $0$ on an unbounded set. It covers a maximum and also a supremum that is not attained.
-- source:
--   Gallego, Berbeglia, Bounds and Heuristics for Multi-Product Personalized Pricing, arXiv:2102.03038v2, §2, p.3

import Mathlib
import Definitions.Def_SingleFactorPricing_LogBound_aggregateProfit

open MeasureTheory

namespace SingleFactorPricing.LogBound

/-- **The single-factor profit** `Rᶠ`. Gallego, Berbeglia, arXiv:2102.03038v2, §2, p.3: "pricing is
done along a positive vector `f`, with `Rᶠ := max_{q>0} R(qf)`."

**Formalization Note.** `IsLUB` rather than a real `⨆`, which would be `0` on an unbounded set.
It covers the paper's max and also a supremum that is not attained. -/
def IsSingleFactorOptimum {N T : Type*} [Fintype N] [MeasurableSpace T] (μ : Measure T)
    (d : T → (N → ℝ) → N → ℝ) (f : N → ℝ) (Rf : ℝ) : Prop :=
  IsLUB ((fun q : ℝ => aggregateProfit μ d (q • f)) '' Set.Ioi 0) Rf

end SingleFactorPricing.LogBound


