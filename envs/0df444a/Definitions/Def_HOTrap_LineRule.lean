-- Prove2me | Definitions.Def_HOTrap_LineRule
-- name    : HOTrap_LineRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:46:06.24024+00:00
-- url     : https://prove2.me/theorems/25f9e347-939d-469a-aec1-052449c62b6e
-- title:
--   Nonadaptive line-integration rule
-- statement:
--   A rule that, given endpoints $u,v$ and a parameter $\theta$, chooses finitely many query points before seeing any answer and then computes a real estimate from the answers.
--
--   This is the object of Lemma 4.2: "one nonadaptive batch of exact gradient queries".
--
--   **Formalization Note** The parameter is the accuracy for the deterministic rule and (accuracy, failure budget, seed) for the randomized rule. Answers are given as a sequence so that measurability of the rule makes sense.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Lemma 4.2, pp.22–23

import Mathlib

namespace HOTrap

/-- **A nonadaptive line-integration rule** with parameter space `Θ`, as in Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Lemma 4.2, pp.22–23.
From the endpoints `u, v` and a parameter `θ`, the rule chooses `count u v θ` query points `node u v θ i`,
all before seeing any answer, and then computes `est u v θ a` from the sequence `a` of answers.

**Formalization Note** The parameter is the accuracy `ε₀` for the deterministic rule, and the triple
(accuracy, failure budget, seed) for the randomized rule. Answers are a sequence so that the rule can be
measurable; `LineRule.estimate` fills the positions from `count` onward with `0`. The rule is not given
the objective. -/
structure LineRule (d : ℕ) (Θ : Type) where
  /-- Number of gradient queries. -/
  count : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → Θ → ℕ
  /-- The `i`-th query point. -/
  node : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → Θ → ℕ → EuclideanSpace ℝ (Fin d)
  /-- The estimate computed from the answers. -/
  est : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → Θ → (ℕ → EuclideanSpace ℝ (Fin d)) → ℝ

end HOTrap


