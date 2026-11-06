-- Prove2me | Definitions.Def_IntervalToDynamic_OnlineAlgorithm
-- name    : IntervalToDynamic_OnlineAlgorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:46.470201+00:00
-- url     : https://prove2.me/theorems/e1a16875-079d-4c38-8690-35db74da79c7
-- title:
--   An online algorithm: a map from loss histories to decisions
-- statement:
--   An **online algorithm** on a space $E$ is a deterministic map from the list of full losses seen so far to the next decision.
--
--   **Formalization Note** The horizon is fixed before the algorithm in every statement, so horizon-aware algorithms are covered.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Algorithm 1, p.8

import Mathlib

namespace IntervalToDynamic

/-- An online algorithm: a deterministic map from the full losses seen so far to the next decision.
Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Algorithm 1, p.8 ("Feed A the full loss `h_t`").

**Formalization Note.** The list holds the losses of rounds `1, …, t − 1`, oldest first. A
horizon-aware algorithm is covered because the horizon `T` is fixed before `A` in every statement. -/
abbrev OnlineAlgorithm (E : Type*) : Type _ := List (E → ℝ) → E

end IntervalToDynamic


