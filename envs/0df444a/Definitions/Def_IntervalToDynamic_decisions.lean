-- Prove2me | Definitions.Def_IntervalToDynamic_decisions
-- name    : IntervalToDynamic_decisions
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:20:57.235926+00:00
-- url     : https://prove2.me/theorems/f1a8f26b-2d30-4291-8ec6-207c80b85810
-- title:
--   The decision of an algorithm at round $t$ against a loss sequence
-- statement:
--   The decision of $\mathcal A$ at round $t\ge1$ against the loss sequence $h$ is $\mathcal A$ applied to the list $[h_1,\dots,h_{t-1}]$. At round $1$ the list is empty.
--
--   **Formalization Note** Rounds are numbered from $1$; round $0$ is unused.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Algorithm 1, p.8

import Mathlib
import Definitions.Def_IntervalToDynamic_OnlineAlgorithm

namespace IntervalToDynamic

/-- The decision of `A` at round `t ≥ 1` against the loss sequence `h`: `A` applied to the list
`[h 1, …, h (t − 1)]`. At round 1 the list is empty. Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Algorithm 1, p.8.

**Formalization Note.** Rounds are numbered from 1; round 0 is unused. -/
def decisions {E : Type*} (A : OnlineAlgorithm E) (h : ℕ → E → ℝ) (t : ℕ) : E :=
  A ((List.range' 1 (t - 1)).map h)

end IntervalToDynamic


