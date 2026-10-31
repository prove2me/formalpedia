-- Prove2me | Definitions.Def_RiskBargaining_Rule
-- name    : RiskBargaining_Rule
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:25:59.396726+00:00
-- url     : https://prove2.me/theorems/acefcc7a-60ca-430b-a60d-50b4dca89970
-- title:
--   A rule over all finite nonempty player sets
-- statement:
--   A **rule** assigns to every finite nonempty player set $N$ and every instance with player set $N$ a vector in $\mathbb R^N$.
--
--   Rules are the objects on which Axioms 1–3 are stated. The player set must vary, because Axiom 3 compares an instance with one that has more players.
--
--   **Formalization Note** Player sets are finite nonempty types in `Type`. The type-class data `Fintype` and `DecidableEq` are subsingletons, so a rule cannot depend on them.
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, Definition 3, p.8

import Mathlib
import Definitions.Def_RiskBargaining_Instance

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **A rule**: a vector of acceptability values for each instance, over all finite nonempty player
types.
Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, Definition 3, p.8.

**Formalization Note.** The domain must vary over player sets, because Axiom 3 relates an instance to
one with a different player set. `n ≥ 1`, implicit in `N = {1, …, n}`, is `Nonempty ι`. The instance
arguments `Fintype` and `DecidableEq` are subsingletons, so a rule cannot depend on them. -/
abbrev Rule (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (X : Type*) [TopologicalSpace X] [CompactSpace X] :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι], Instance μ p X ι → ι → ℝ

end RiskBargaining


