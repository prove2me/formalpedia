-- Prove2me | Definitions.Def_CohenPriceFairness_LocalWelfare_FairPricing
-- name    : CohenPriceFairness_LocalWelfare_FairPricing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:21:34.958391+00:00
-- url     : https://prove2.me/theorems/5a7398de-6e9f-467a-b44c-b983d1b78470
-- title:
--   Fairness metrics and global optimal pricing selections
-- statement:
--   There are four distinct metrics: $M_i(p)=p,q_i(p),S_i(p),N_i(p)$. A baseline $b=(b_0,b_1)$ is optimal if each $b_i\ge0$ maximizes $R_i$ against every nonnegative real price. For a chosen metric let $g_M(p)=|M_0(p_0)-M_1(p_1)|$.
--
--   For $\alpha\in[0,1]$, a pair $p$ is feasible exactly when both prices are nonnegative and $g_M(p)\le(1-\alpha)g_M(b)$. A fair optimum is a feasible pair whose total profit is at least that of every feasible pair. Each metric defines a separate problem.
--
--   A local optimal selection is any function $P:\mathbb R\to\mathbb R^2$ with $P(0)=b$ for which some $0<\varepsilon\le1$ satisfies: $P(\alpha)$ is a fair global optimum for every $\alpha\in[0,\varepsilon]$. Values outside this interval are immaterial. There is no smoothness, uniqueness, interiority, positive demand, or positive-gap condition on a selection. Below-cost prices, zero gaps, and no-sales optima remain allowed.
-- source:
--   Cohen, Elmachtoub and Lei (2022), Price Discrimination with Fairness Constraints, Management Science, https://doi.org/10.1287/mnsc.2022.4317; published artifact, PDF pages = printed pages; SHA-256 b3f8804f1610eb36d8a2ef32e836f4a65285e6b8ad427f7c82172e7a3fd73147; Eq. (1), p. 7, and pp. 7–8, 12 (optimal policies).

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Market

namespace CohenPriceFairness.LocalWelfare

inductive Metric where
  | price | demand | surplus | nonbuyer
  deriving DecidableEq

noncomputable def metricValue (m : Market) : Metric → Fin 2 → ℝ → ℝ
  | .price => fun _ p => p
  | .demand => demand m
  | .surplus => surplus m
  | .nonbuyer => nonbuyer m

/-- All individual global maximizers on nonnegative prices. -/
def BaselineOptimal (m : Market) (b : Prices) : Prop :=
  ∀ i, 0 ≤ b i ∧ ∀ p : ℝ, 0 ≤ p → profit m i p ≤ profit m i (b i)

noncomputable def gap (m : Market) (k : Metric) (p : Prices) : ℝ :=
  |metricValue m k 0 (p 0) - metricValue m k 1 (p 1)|

/-- Equation (1), including its full parameter and price domains. -/
def FairFeasible (m : Market) (b : Prices) (k : Metric) (α : ℝ) (p : Prices) : Prop :=
  α ∈ Set.Icc 0 1 ∧ (∀ i, 0 ≤ p i) ∧ gap m k p ≤ (1 - α) * gap m k b

/-- The optimum set is defined by comparison against every feasible price pair. -/
def FairOptimal (m : Market) (b : Prices) (k : Metric) (α : ℝ) (p : Prices) : Prop :=
  FairFeasible m b k α p ∧
    ∀ q : Prices, FairFeasible m b k α q → totalProfit m q ≤ totalProfit m p

/-- A selection of actual optima on some right neighborhood, anchored at the baseline.
No continuity or differentiability, and no restriction to active price neighborhoods. -/
def LocalOptimalSelection (m : Market) (b : Prices) (k : Metric)
    (P : ℝ → Prices) : Prop :=
  P 0 = b ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
    ∀ α ∈ Set.Icc 0 ε, FairOptimal m b k α (P α)

end CohenPriceFairness.LocalWelfare

/- Imported definition source (verbatim dependency snapshot for standalone inspection).

import Mathlib

open MeasureTheory

namespace CohenPriceFairness.LocalWelfare

/-- A nonnegative valuation law with a finite first moment (pp. 6–7). -/
def ValuationLaw (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ (∀ᵐ v ∂μ, 0 ≤ v) ∧ Integrable (fun v : ℝ => v) μ

end CohenPriceFairness.LocalWelfare

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_ValuationLaw

open MeasureTheory

namespace CohenPriceFairness.LocalWelfare

/-- Two marginal valuation laws, real population masses, and common marginal cost. -/
structure Market where
  law : Fin 2 → Measure ℝ
  population : Fin 2 → ℝ
  cost : ℝ

/-- The general distribution-based market conventions, pp. 6–7. -/
def Market.Admissible (m : Market) : Prop :=
  0 ≤ m.cost ∧ ∀ i, 0 < m.population i ∧ ValuationLaw (m.law i)

noncomputable def demand (m : Market) (i : Fin 2) (p : ℝ) : ℝ :=
  (m.law i (Set.Ici p)).toReal

noncomputable def surplus (m : Market) (i : Fin 2) (p : ℝ) : ℝ :=
  ∫ v, max (v - p) 0 ∂m.law i

/-- Conditional mean of nonbuyers; explicitly zero on a null conditioning event. -/
noncomputable def nonbuyer (m : Market) (i : Fin 2) (p : ℝ) : ℝ :=
  if m.law i (Set.Iio p) = 0 then 0
  else (∫ v in Set.Iio p, v ∂m.law i) / (m.law i (Set.Iio p)).toReal

noncomputable def profit (m : Market) (i : Fin 2) (p : ℝ) : ℝ :=
  m.population i * (p - m.cost) * demand m i p

abbrev Prices := Fin 2 → ℝ

noncomputable def totalProfit (m : Market) (p : Prices) : ℝ :=
  profit m 0 (p 0) + profit m 1 (p 1)

/-- Group-specific surplus indices, as on pp. 7 and 31. -/
noncomputable def welfare (m : Market) (p : Prices) : ℝ :=
  totalProfit m p + m.population 0 * surplus m 0 (p 0) +
    m.population 1 * surplus m 1 (p 1)

end CohenPriceFairness.LocalWelfare
-/


