-- Prove2me | Definitions.Def_GreedyRS_Tight_Setting
-- name    : GreedyRS_Tight_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:28:55.179273+00:00
-- url     : https://prove2.me/theorems/536b4eb9-a6c2-4d01-8e82-89188d9648da
-- title:
--   p. ec4 — N_i(min_{1≤n≤m} X̄₁(n)), the first time a path drops below the running minimum of another up to m (X̄₁(0) = ∞ convention)
-- statement:
--   This file adds one object to the shared model of Li, Fan and Hong's analysis of the greedy procedure (running averages $\bar X_i(n)$, the greedy procedure, the normal observation array, $C(x)$ and boundary-crossing times, all defined in the shared setting `GreedyRS.Greedy.Setting`).
--
--   For two real paths $y_i(n)$ and $y(n)$ ($n \in \mathbb N$) and an integer $m \ge 0$, define
--   $$N_i\Big(\min_{1 \le j \le m} y(j)\Big) = \inf\Big\{n \ge 1 : y_i(n) < y(j) \text{ for all } 1 \le j \le m\Big\} \in \{1, 2, \dots\} \cup \{+\infty\},$$
--   the first time $n \ge 1$ at which $y_i$ lies strictly below every value $y(1), \dots, y(m)$, i.e. strictly below their minimum; it is $+\infty$ if this never happens. For $m = 0$ the condition is empty and the value is $1$.
--
--   With $y_i = \bar X_i$ and $y = \bar X_1$ this is the boundary-crossing time $N_i(\min_{1 \le n \le m} \bar X_1(n))$ of (EC.1.8): the number of observations alternative $i$ needs before its running average falls below the lowest running average alternative 1 has shown in its first $m$ observations.
--
--   **Formalization Note.** The value is in `ℕ∞`, so "never" is $+\infty$ and not the junk value $0$. The case $m = 0$ encodes the paper's convention "When $m_\epsilon = 1$, we set $\bar X_1(m_\epsilon - 1) = \bar X_1(0) = \infty$" (p. ec4), since $N_i(\infty) = 1$; the minimum over the empty range is never taken as a real infimum.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, p. ec4, (EC.1.8) and the convention X̄_1(0) = ∞

import Mathlib
import Definitions.Def_GreedyRS_Greedy_Setting

namespace GreedyRS.Tight

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- `N_i(min_{1 ≤ j ≤ m} X̄_1(j)) = inf {n ≥ 1 : yi n < y j for all 1 ≤ j ≤ m}`, the first time the
path `yi` drops strictly below every value `y 1, …, y m` (`⊤` if never). For `m = 0` the condition
is empty and the value is `1`: the paper's convention `X̄_1(0) = ∞`, `N_i(∞) = 1`. -/
noncomputable def prefixCross (yi y : ℕ → ℝ) (m : ℕ) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : 1 ≤ n ∧ ∀ j ∈ Finset.Icc 1 m, yi n < y j), (n : ℕ∞)

end GreedyRS.Tight


