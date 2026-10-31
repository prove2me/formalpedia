-- Prove2me | Definitions.Def_RiskBargaining_Instance_v
-- name    : RiskBargaining_Instance_v
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:25:53.912718+00:00
-- url     : https://prove2.me/theorems/8e8a7809-2756-4079-92fd-3c26e37f39dd
-- title:
--   The values $v_i=\mathcal A_i(R_i)$
-- statement:
--   For an instance $(R,M,\mathcal A)$ and a player $i$, the **value** of player $i$ is
--   $$
--   v_i=\mathcal A_i(R_i).
--   $$
--   It is the player's personal evaluation of the opportunity loss. It is the disagreement point of the bargaining game and determines the player's share in rule (9).
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, §2.2, p.8

import Mathlib
import Definitions.Def_RiskBargaining_Instance

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {X : Type*} [TopologicalSpace X] [CompactSpace X] {ι : Type*}

/-- **The values** `v_i = 𝒜_i(R_i)`.
Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, §2.2, p.8. -/
def Instance.v (I : Instance μ p X ι) (i : ι) : ℝ :=
  I.A i (I.R i)

end RiskBargaining


