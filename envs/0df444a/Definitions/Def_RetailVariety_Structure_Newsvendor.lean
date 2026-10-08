-- Prove2me | Definitions.Def_RetailVariety_Structure_Newsvendor
-- name    : RetailVariety_Structure_Newsvendor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:22.637867+00:00
-- url     : https://prove2.me/theorems/bfd8a51c-d1a6-47b5-95e9-24ddfbb95695
-- title:
--   Single-variant newsvendor profit $E[p\min\{x,Y\}-cx]$ and the two demand laws (normal; scaled Bernoulli (3))
-- statement:
--   This file fixes the stocking problem of one variant in the van Ryzin–Mahajan model.
--
--   1. **Expected profit.** If $x$ units are stocked, demand $Y$ has law $P$, the price is $p$ and the unit cost is $c$, the expected profit is
--   $$E\bigl[p\min\{x,Y\}-cx\bigr]=\int\bigl(p\min\{x,y\}-cx\bigr)\,P(dy).$$
--   2. **Independent-population demand** (§2.3.1): a variant with choice probability $q$ in a store of volume $\lambda$ has normal demand with mean $\lambda q$ and standard deviation $\sigma(\lambda q)^\beta$,
--   $$Y\sim N\bigl(\lambda q,\ (\sigma(\lambda q)^\beta)^2\bigr).$$
--   3. **Trend-following demand** (3): $Y$ is a scaled Bernoulli variable,
--   $$P(Y=\lambda)=q,\qquad P(Y=0)=1-q .$$
--
--   The store profit (4) is the maximum over stocking vectors $x\ge 0$ of the sum of these single-variant profits over the offered variants.
--
--   **Formalization Note** The normal law is Mathlib's `gaussianReal` with variance $(\sigma(\lambda q)^\beta)^2$ (as a nonnegative real); the Bernoulli law is $q\,\delta_\lambda+(1-q)\,\delta_0$ with weights `ENNReal.ofReal q` and `ENNReal.ofReal (1-q)`, a probability measure whenever $0\le q\le 1$. The expectation is a Bochner integral; it is finite under both laws.
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, pp. 1501–1502, §2.3.1, eq. (3), §2.4.1 eq. (4)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace RetailVariety.Structure

/-- Expected single-variant profit `E[p min{x, Y} - c x]` when `x` units are stocked and the
demand `Y` has law `P` (§2.4.1, p. 1502). -/
noncomputable def newsvendorProfit (P : Measure ℝ) (p c x : ℝ) : ℝ :=
  ∫ y, (p * min x y - c * x) ∂P

/-- Independent-population demand law of a variant with choice probability `q` (§2.3.1, p. 1501):
normal with mean `λ q` and standard deviation `σ (λ q)^β`. -/
noncomputable def normalDemand (lam σ β q : ℝ) : Measure ℝ :=
  gaussianReal (lam * q) (Real.toNNReal ((σ * (lam * q) ^ β) ^ 2))

/-- Trend-following demand law (3), p. 1501: the scaled Bernoulli law with
`P(Y = λ) = q` and `P(Y = 0) = 1 - q`. -/
noncomputable def trendDemand (lam q : ℝ) : Measure ℝ :=
  ENNReal.ofReal q • Measure.dirac lam + ENNReal.ofReal (1 - q) • Measure.dirac 0

end RetailVariety.Structure


