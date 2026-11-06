-- Prove2me | Definitions.Def_IntervalToDynamic_greedyPartition
-- name    : IntervalToDynamic_greedyPartition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:23:03.39621+00:00
-- url     : https://prove2.me/theorems/ee82fcd0-3c13-4ec7-a735-ad44ea59321a
-- title:
--   Lemma 11: the Baby–Wang hindsight partition of $[T]$
-- statement:
--   For $B>0$, $\varepsilon\ge0$ and a sequence $u$, the partition of $[T]$ built from left to right, greedily extending each interval $I$ as long as possible subject to $P_I\le B/|I|^\varepsilon$. It is a list of intervals $(a,b)$.
--
--   This partition is used only in the analysis, in hindsight.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Lemma 11, p.29

import Mathlib
import Definitions.Def_IntervalToDynamic_greedyPartitionFrom

namespace IntervalToDynamic

/-- The Baby–Wang hindsight partition of `[T]`, as a list of intervals `(a, b)` from left to right:
"Partition `[T]` from left to right, greedily extending each interval `I` as long as possible subject
to `P_I ≤ B/|I|^ε`". Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Lemma 11, p.29. -/
noncomputable def greedyPartition {E : Type*} [NormedAddCommGroup E] (B ε : ℝ) (u : ℕ → E) (T : ℕ) :
    List (ℕ × ℕ) :=
  greedyPartitionFrom B ε u T T 1

end IntervalToDynamic


