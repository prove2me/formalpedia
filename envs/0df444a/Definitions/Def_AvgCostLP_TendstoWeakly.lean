-- Prove2me | Definitions.Def_AvgCostLP_TendstoWeakly
-- name    : AvgCostLP_TendstoWeakly
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:27:42.916838+00:00
-- url     : https://prove2.me/theorems/9e31813f-1761-4f97-94e3-27e513b2cc70
-- title:
--   Weak convergence $\mu_n\xrightarrow{w}\mu$ of measures
-- statement:
--   A sequence of measures $\mu_n$ on a topological space $Y$ **converges weakly** to $\mu$, $\mu_n\xrightarrow{w}\mu$, if
--   $$\int f\,d\mu_n\to\int f\,d\mu\qquad\text{for every bounded continuous }f:Y\to\mathbb R .$$
--   This is the topology of weak convergence on $\mathcal P(Y)$ used throughout §5.1.1.
-- source:
--   Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, §2, pp.4-5, and §5.1.1, p.22

import Mathlib

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

namespace AvgCostLP

/-- Weak convergence `μ_n →ʷ μ` of a sequence of (probability) measures (Yu, arXiv:1905.12095v3,
§2, p.4–5, and §5.1.1, p.22): `∫ f dμ_n → ∫ f dμ` for every bounded continuous `f : Y → ℝ`. -/
def TendstoWeakly {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    (μs : ℕ → Measure Y) (μ : Measure Y) : Prop :=
  ∀ f : Y →ᵇ ℝ, Tendsto (fun n => ∫ y, f y ∂(μs n)) atTop (𝓝 (∫ y, f y ∂μ))

end AvgCostLP


