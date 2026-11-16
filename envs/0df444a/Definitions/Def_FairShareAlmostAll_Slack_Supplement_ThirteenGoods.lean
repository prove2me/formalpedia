-- Prove2me | Definitions.Def_FairShareAlmostAll_Slack_Supplement_ThirteenGoods
-- name    : FairShareAlmostAll_Slack_Supplement_ThirteenGoods
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:08:26.905401+00:00
-- url     : https://prove2.me/theorems/6d47dd05-71d5-4cf7-a047-8a03898485f7
-- title:
--   The thirteen-goods valuation and its weighted bundle family
-- statement:
--   Let $G=\{1,\dots,13\}$ be a set of goods with the nonnegative additive valuation
--
--   $$(v(1),\dots,v(13))=(137,135,119,79,77,76,54,50,49,10,9,8,6).$$
--
--   The weighted family $\mathcal Q$ consists of the thirteen bundles, with weights $\tau_P$,
--
--   $$\{4,5\}:\tfrac12,\ \{4,6\}:\tfrac12,\ \{5,6\}:\tfrac12,\ \{2,7\}:\tfrac15,\ \{3,7\}:\tfrac15,\ \{3,8\}:\tfrac25,\ \{3,9\}:\tfrac25,$$
--
--   $$\{7,8,9\}:\tfrac35,\ \{2,10,11\}:\tfrac15,\ \{2,10,12\}:\tfrac15,\ \{1,11,12\}:\tfrac25,\ \{1,10,13\}:\tfrac35,\ \{2,11,12,13\}:\tfrac25.$$
--
--   This instance (Table 2 of Moulin and Saberi's skiving-stock examples, as cited by the paper) is the base of the paper's linear upper bound on the entitlement cap: its weighted family is a fractional certificate while no five disjoint bundles reach value $153$.
--
--   **Formalization Note** Goods are `Fin 13`, and paper good $g$ is the Lean index $g-1$; the bundles are indexed by `Fin 13` in table order. The value column of the paper's table is derived, not stored.
-- source:
--   Tomer Ezra, Tamar Garbuz, Fair Share Allocations for Almost All Agents, STOC 2027 submission #480 (October 2026), printed pp. 19–20 (PDF pp. 20–21), §5.1 and its table; source.pdf SHA256 c9f47a54f6a9e1568951e8e3845ff79c34d51d391a68fd697d37d8ba29cc7491

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic

namespace FairShareAlmostAll.Slack.Supplement

/-- §5.1, PDF p. 20: the thirteen singleton values. Paper good `g + 1` is `g : Fin 13`. -/
def thirteenValue : Fin 13 → ℝ :=
  ![137, 135, 119, 79, 77, 76, 54, 50, 49, 10, 9, 8, 6]

/-- §5.1, PDF p. 21: the thirteen bundles of the table, in table order, with every paper good
shifted down by one (paper `{4, 5}` is `{3, 4}`). -/
def thirteenBundle : Fin 13 → Finset (Fin 13) :=
  ![{3, 4}, {3, 5}, {4, 5}, {1, 6}, {2, 6}, {2, 7}, {2, 8}, {6, 7, 8},
    {1, 9, 10}, {1, 9, 11}, {0, 10, 11}, {0, 9, 12}, {1, 10, 11, 12}]

/-- §5.1, PDF p. 21: the weight `τ_P` of each table bundle (last column of the table). -/
noncomputable def thirteenWeight : Fin 13 → ℝ :=
  ![1/2, 1/2, 1/2, 1/5, 1/5, 2/5, 2/5, 3/5, 1/5, 1/5, 2/5, 3/5, 2/5]

end FairShareAlmostAll.Slack.Supplement


