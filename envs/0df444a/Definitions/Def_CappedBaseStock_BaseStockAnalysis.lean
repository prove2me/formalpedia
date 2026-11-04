-- Prove2me | Definitions.Def_CappedBaseStock_BaseStockAnalysis
-- name    : CappedBaseStock_BaseStockAnalysis
-- status  : Definition
-- author  : @StellaXin
-- created : 2026-09-08T02:21:58.805824+00:00
-- url     : https://prove2.me/theorems/d7bcd239-3505-42ef-9d27-67690324a999
-- title:
--   Ordinary base-stock average lost sales and overlapping demand scans
-- statement:
--   Let demand be i.i.d., nonnegative, with finite positive mean, and let the lead time be an integer $L\ge1$. Use the inventory dynamics and empty initial state of the CappedBaseStock model. For ordinary base stock at level $S\ge0$, let $\ell_t$ denote lost sales. Define its long-run expected average lost sales by
--
--   $$\overline\ell_S=\limsup_{N\to\infty}\frac1N\sum_{t=0}^{N-1}\mathbb E[\ell_t].$$
--
--   For a nonnegative demand path $d=(d_i)_{i\ge0}$, define the scan over the $L+1$ overlapping demand windows of length $L+1$ by
--
--   $$V_L(d)=\max_{0\le j\le L}\sum_{i=0}^{L}d_{j+i},\qquad X_L(d,S)=(V_L(d)-S)^+.$$
--
--   The scan uses exactly the coordinates $0,\ldots,2L$. Its stock threshold may be any real number; the policy level itself is nonnegative. These definitions separate the demand-only overload quantity from the actual policy's lost sales and support the ordinary-base-stock cost analysis.
--
--   **Formalization Note** Expectations and the limsup average loss take values in the extended nonnegative reals. `baseStockAverageLoss` uses the original model's `averageCost` operator and its same zero-start trajectory, with lost sales replacing monetary period cost. This definition file asserts no stationarity, convergence, or inequality.
-- source:
--   Linwei Xin, Capped Base-Stock Policies: A 2.33-Approximation, author-supplied LaTeX manuscript (756 lines), SHA-256 f353793c255e1ebed5f3ec541037284bd926183e3e5b71941f13e79c2d67cb7a. Public paper listing: https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7134538. Equations `eq-V`, `eq-scan-bound`, and `eq-loss-comparison`, lines 525–550; scan represented with zero-based coordinates as in lines 585–597. The average-loss definition uses the zero-start limsup objective of the mission.

import Definitions.Def_CappedBaseStock_Model

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace CappedBaseStock

/-- Expected average lost sales of the ordinary base-stock rule, measured by
the same zero-start Cesaro limsup as the original cost objective. -/
def baseStockAverageLoss (P : DemandLaw) (c : Parameters) (S : ℝ≥0) : ℝ≥0∞ :=
  averageCost P (fun t ω =>
    (lostSales c (cbsRun c S S ω t) (ω.1 t) : ℝ≥0∞))

/-- The largest total demand in the L+1 overlapping windows of length L+1
inside a block of 2L+1 demands. -/
def scanDemand (d : DemandPath) (L : ℕ) : ℝ :=
  (Finset.range (L + 1)).sup' (by simp) (fun j =>
    ∑ i ∈ Finset.range (L + 1), (d (j + i) : ℝ))

/-- Positive overload of the demand scan above a real stock level. -/
def scanExcess (d : DemandPath) (L : ℕ) (S : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (scanDemand d L - S)

end CappedBaseStock


