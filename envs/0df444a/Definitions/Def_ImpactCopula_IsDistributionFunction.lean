-- Prove2me | Definitions.Def_ImpactCopula_IsDistributionFunction
-- name    : ImpactCopula_IsDistributionFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:53:06.332691+00:00
-- url     : https://prove2.me/theorems/eeed768a-1bfa-4cbd-99d4-ec5efa284201
-- title:
--   Distribution function on $\mathbb R$
-- statement:
--   A function $f : \mathbb R \to \mathbb R$ is a **distribution function** if it is non-decreasing, right-continuous, and
--
--   $$
--   \lim_{v \to -\infty} f(v) = 0, \qquad \lim_{v \to +\infty} f(v) = 1 .
--   $$
--
--   Its values then lie in $[0,1]$, and it is the distribution function of a probability measure on $\mathbb R$.
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), Lemma 2, p.75 (PDF p.78); Remark 1 (i), p.42 (PDF p.45)

import Mathlib

open Filter Topology

namespace ImpactCopula

/-- A distribution function on `ℝ` (used in Lemma 2, p.75, PDF p.78, and Remark 1 (i), p.42,
PDF p.45), Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024): a non-decreasing, right-continuous function `f : ℝ → [0, 1]` with
`f(v) → 0` as `v → −∞` and `f(v) → 1` as `v → +∞`.

**Formalization Note.** The values lie in `[0, 1]` as a consequence of monotonicity and the two
limits, so the codomain is `ℝ`. -/
def IsDistributionFunction (f : ℝ → ℝ) : Prop :=
  Monotone f ∧ (∀ x : ℝ, ContinuousWithinAt f (Set.Ici x) x) ∧
    Tendsto f atBot (𝓝 0) ∧ Tendsto f atTop (𝓝 1)

end ImpactCopula


