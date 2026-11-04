-- Prove2me | Definitions.Def_LostSalesOrderUpTo_Asymptotic_Backorder
-- name    : LostSalesOrderUpTo_Asymptotic_Backorder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T08:29:00.630735+00:00
-- url     : https://prove2.me/theorems/e915fa2d-9d77-4ad9-8f18-b3032f06e6ec
-- title:
--   Lead-time demand and backorder benchmarks
-- statement:
--   Let $P$ be the law of one nonnegative demand and let $\tau$ be the replenishment lead time. The **lead-time demand** $\mathbf D$ is the sum of $\tau+1$ independent draws from $P$. Its distribution function is $F(y)=\Pr(\mathbf D\le y)$. For a backorder system with holding rate $h$, shortage rate $b$, and level $S\ge0$, the stationary cost is
--
--   $$C^{\mathcal B,S}(h,b)=h\mathbb E[(S-\mathbf D)^+]+b\mathbb E[(\mathbf D-S)^+].$$
--
--   The best backorder cost is the infimum over nonnegative levels. The newsvendor level is the smallest $S$ whose distribution probability reaches $b/(b+h)$. The ratio $\psi(S;h,b)$ divides expected shortage charge by expected holding charge. The mean residual life is $\mathbb E[\mathbf D-t\mid\mathbf D>t]$ when that conditioning event has positive probability and zero otherwise. Assumption 1 requires $m_{\mathbf D}(t)/t\to0$ as $t\to\infty$.
--
--   These objects provide the common benchmarks for the finite-penalty and asymptotic comparisons.
--
--   **Formalization Note** The Bochner expectations are used for finite-mean laws; the ratio is used only where its holding-cost denominator is positive.
-- source:
--   Huh, Janakiraman, Muckstadt & Rusmevichientong, Asymptotic Optimality of Order-up-to Policies in Lost Sales Inventory Systems, working paper, December 4, 2006 (preprint of Management Science 55(3), 2009, DOI 10.1287/mnsc.1080.0945), p. 3, §1.1 and §3–4, pp. 3–4, 9, 11–12

import Definitions.Def_CappedBaseStock_Model

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesOrderUpTo.Asymptotic

/-- The law of demand over the order period and the following lead time. -/
def leadTimeLaw (P : CappedBaseStock.DemandLaw) (τ : ℕ) : Measure ℝ≥0 :=
  Measure.map (fun d : CappedBaseStock.DemandPath =>
    ∑ i ∈ Finset.range (τ + 1), d i) (CappedBaseStock.demandPathLaw P)

/-- Distribution function of the lead-time demand. -/
def distribution (μ : Measure ℝ≥0) (y : ℝ≥0) : ℝ≥0∞ := μ (Set.Iic y)

/-- Expected positive inventory and shortfall, respectively. -/
def expectedHolding (μ : Measure ℝ≥0) (S : ℝ≥0) : ℝ :=
  ∫ d : ℝ≥0, max ((S : ℝ) - (d : ℝ)) 0 ∂μ

def expectedShortfall (μ : Measure ℝ≥0) (S : ℝ≥0) : ℝ :=
  ∫ d : ℝ≥0, max ((d : ℝ) - (S : ℝ)) 0 ∂μ

/-- Stationary order-up-to cost in the backorder system. -/
def backorderCost (μ : Measure ℝ≥0) (h b : ℝ) (S : ℝ≥0) : ℝ :=
  h * expectedHolding μ S + b * expectedShortfall μ S

/-- Best order-up-to cost in the backorder system. -/
def backorderOptimalCost (μ : Measure ℝ≥0) (h b : ℝ) : ℝ :=
  sInf (Set.range (backorderCost μ h b))

/-- Smallest critical-fractile level for the lead-time demand. -/
def newsvendorLevel (μ : Measure ℝ≥0) (h b : ℝ) : ℝ≥0 :=
  sInf {S : ℝ≥0 | ENNReal.ofReal (b / (b + h)) ≤ distribution μ S}

/-- Ratio of expected shortage charge to expected holding charge. -/
def shortageHoldingRatio (μ : Measure ℝ≥0) (h b : ℝ) (S : ℝ≥0) : ℝ :=
  b * expectedShortfall μ S / (h * expectedHolding μ S)

/-- Conditional expected excess over a threshold, with zero at and beyond the upper endpoint. -/
def meanResidualLife (μ : Measure ℝ≥0) (t : ℝ) : ℝ :=
  if 0 < (μ {d : ℝ≥0 | t < (d : ℝ)}).toReal then
    (∫ d : ℝ≥0, max ((d : ℝ) - t) 0 ∂μ) /
      (μ {d : ℝ≥0 | t < (d : ℝ)}).toReal
  else 0

/-- Assumption 1 on the lead-time demand law. -/
def AssumptionOne (μ : Measure ℝ≥0) : Prop :=
  Tendsto (fun t : ℝ => meanResidualLife μ t / t) atTop (nhds 0)

end LostSalesOrderUpTo.Asymptotic


