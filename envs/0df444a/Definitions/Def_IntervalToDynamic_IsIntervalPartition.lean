-- Prove2me | Definitions.Def_IntervalToDynamic_IsIntervalPartition
-- name    : IntervalToDynamic_IsIntervalPartition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:51.725526+00:00
-- url     : https://prove2.me/theorems/79507c83-9b42-4869-ac61-4cadc06df2a7
-- title:
--   Consecutive nonempty intervals covering $[a,T]$
-- statement:
--   A list of pairs $(a_1,b_1),\dots,(a_K,b_K)$ is a partition of $[a,T]$ into consecutive nonempty intervals when $a_1=a$, $a_j\le b_j$, $a_{j+1}=b_j+1$ and $b_K=T$. For $a=1$ this is a partition of $[T]$.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Lemma 11, p.29; Eq. (15), p.10

import Mathlib

namespace IntervalToDynamic

/-- `L` is a list of consecutive nonempty intervals `(a, b)` that starts at `a` and covers `[a, T]`.
Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Lemma 11, p.29, and Eq. (15), p.10.

**Formalization Note.** `IsIntervalPartition T 1 L` says that `L` is a partition of `[T]`. -/
def IsIntervalPartition (T : ℕ) : ℕ → List (ℕ × ℕ) → Prop
  | a, [] => a = T + 1
  | a, p :: L => p.1 = a ∧ p.1 ≤ p.2 ∧ IsIntervalPartition T (p.2 + 1) L

end IntervalToDynamic


