-- Prove2me | Definitions.Def_RiskBargaining_nashRule
-- name    : RiskBargaining_nashRule
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:29:07.778248+00:00
-- url     : https://prove2.me/theorems/9bd11067-dd85-4817-aba5-41833b1851c5
-- title:
--   The rule (9)
-- statement:
--   The rule (9) is
--   $$
--   u_i=\frac{v_i}{\sum_{j=1}^n v_j}\cdot z(R,M,\mathcal A),\qquad i\in N,
--   $$
--   where $v_i=\mathcal A_i(R_i)$ and $z$ is defined by (8). Each player gets a share of the optimal total that is proportional to the acceptability of the endowment.
--
--   **Formalization Note** On an admissible instance the denominator is positive and $z$ is the max of (8). Off the class the formula has no meaning and no statement looks at it.
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, Theorem 1, equation (9), p.10

import Mathlib
import Definitions.Def_RiskBargaining_Rule
import Definitions.Def_RiskBargaining_Instance_v
import Definitions.Def_RiskBargaining_Instance_z

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- **The rule (9)**: `u_i = v_i / (∑_j v_j) · z(R, M, 𝒜)`.
Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, Theorem 1, equation (9), p.10.

**Formalization Note.** On an admissible instance `∑_j v_j > 0` and `z` is the max of (8). Off the class
division by zero and the `sSup` junk value may occur, and no statement looks at those values. -/
noncomputable def nashRule : Rule μ p X :=
  fun _ _ _ _ I i => I.v i / (∑ j, I.v j) * I.z

end RiskBargaining


