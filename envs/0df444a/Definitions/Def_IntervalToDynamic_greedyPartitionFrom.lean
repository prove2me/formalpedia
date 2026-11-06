-- Prove2me | Definitions.Def_IntervalToDynamic_greedyPartitionFrom
-- name    : IntervalToDynamic_greedyPartitionFrom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:22:02.690693+00:00
-- url     : https://prove2.me/theorems/11a321ae-c901-47c7-88d4-de69f3351c81
-- title:
--   The greedy partition from a start point
-- statement:
--   The greedy intervals of $[a,T]$ from left to right: close the interval started at $a$ at its greedy end $b$ and restart at $b+1$, until $T$ is passed.
--
--   **Formalization Note** The recursion carries a step budget (`fuel`). Greedy intervals are nonempty, so a budget of $T$ steps from $a=1$ never runs out early.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Lemma 11 and its proof, p.29

import Mathlib
import Definitions.Def_IntervalToDynamic_greedyEnd

namespace IntervalToDynamic

/-- The greedy partition of `[a, T]` from left to right, with `fuel` steps at most. Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Lemma 11,
p.29.

**Formalization Note.** Every greedy interval is nonempty, so `T` steps suffice from `a = 1`;
`greedyPartition` calls this with `fuel = T`, and the fuel never runs out early. -/
noncomputable def greedyPartitionFrom {E : Type*} [NormedAddCommGroup E] (B ε : ℝ) (u : ℕ → E)
    (T : ℕ) : ℕ → ℕ → List (ℕ × ℕ)
  | 0, _ => []
  | fuel + 1, a =>
      if T < a then []
      else (a, greedyEnd B ε u T a) :: greedyPartitionFrom B ε u T fuel (greedyEnd B ε u T a + 1)

end IntervalToDynamic


