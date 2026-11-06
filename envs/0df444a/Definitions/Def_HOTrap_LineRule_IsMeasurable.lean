-- Prove2me | Definitions.Def_HOTrap_LineRule_IsMeasurable
-- name    : HOTrap_LineRule_IsMeasurable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:47:08.619289+00:00
-- url     : https://prove2.me/theorems/03c2c069-42c1-4cbe-affb-c7d28608caf1
-- title:
--   Measurable line rule
-- statement:
--   A line rule is measurable if its query count, each query point and its estimate are jointly measurable in the endpoints, the parameter and the answers.
--
--   Lemma 4.2 feeds the rule with $\mathcal F$-measurable inputs, so this is what makes the estimate a random variable.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Lemma 4.2, pp.22–23

import Mathlib
import Definitions.Def_HOTrap_LineRule

namespace HOTrap

/-- **Joint measurability of a line rule** in its inputs and answers. Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Lemma 4.2, pp.22–23, feeds
the rule with `F`-measurable inputs, so the estimate must be a measurable function of them. -/
def LineRule.IsMeasurable {d : ℕ} {Θ : Type} [MeasurableSpace Θ] (R : LineRule d Θ) : Prop :=
  Measurable (fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × Θ => R.count q.1 q.2.1 q.2.2) ∧
    (∀ i, Measurable (fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × Θ => R.node q.1 q.2.1 q.2.2 i)) ∧
    Measurable (fun q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × Θ) × (ℕ → EuclideanSpace ℝ (Fin d)) => R.est q.1.1 q.1.2.1 q.1.2.2 q.2)

end HOTrap


