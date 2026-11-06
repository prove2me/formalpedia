-- Prove2me | Definitions.Def_IntervalToDynamic_TwoPieceComparators
-- name    : IntervalToDynamic_TwoPieceComparators
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:20:58.793247+00:00
-- url     : https://prove2.me/theorems/71287891-402e-4305-a20b-202a9edd815b
-- title:
--   The conclusion of Theorem 6: at most two pieces with comparators
-- statement:
--   There is a partition of $[n]$ into $1\le S\le2$ nonempty consecutive pieces $I_s$ and comparators $z_s\in\mathcal Y$ with
--   $$
--   \text{Err}_{[n]}=\sum_{s=1}^S\text{Err}_{I_s}(z_s)\le \text{bound}.
--   $$
--
--   **Formalization Note** $S=1$ is the piece $[1,n]$; $S=2$ is $[1,m]$, $[m+1,n]$ with $1\le m<n$.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Theorem 6, p.10

import Mathlib
import Definitions.Def_IntervalToDynamic_approxError

namespace IntervalToDynamic

/-- The conclusion shape of Theorem 6: there is a partition of `[n]` into `1 ≤ S ≤ 2` nonempty
consecutive pieces `I_s` and an interval comparator `z_s ∈ Y` on each piece with
`Err_[n] = ∑_s Err_{I_s}(z_s) ≤ bound`. Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Theorem 6, p.10.

**Formalization Note.** `S = 1` is the single piece `[1, n]`; `S = 2` is `[1, m]`, `[m + 1, n]` with
`1 ≤ m < n`. -/
def TwoPieceComparators {E : Type*} (Y : Set E) (h : ℕ → E → ℝ) (u : ℕ → E) (n : ℕ) (bound : ℝ) :
    Prop :=
  (∃ z ∈ Y, approxError h u 1 n z ≤ bound) ∨
  ∃ m, 1 ≤ m ∧ m < n ∧ ∃ z₁ ∈ Y, ∃ z₂ ∈ Y,
    approxError h u 1 m z₁ + approxError h u (m + 1) n z₂ ≤ bound

end IntervalToDynamic


