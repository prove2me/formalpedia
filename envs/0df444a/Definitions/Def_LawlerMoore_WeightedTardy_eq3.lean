-- Prove2me | Definitions.Def_LawlerMoore_WeightedTardy_eq3
-- name    : LawlerMoore_WeightedTardy_eq3
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T13:07:41.160593+00:00
-- url     : https://prove2.me/theorems/e7fede68-cbf5-4744-85e6-0adae58fe99b
-- title:
--   Eq. (3) — the recursion f(j, t) = max{f(j, t−1), f(j−1, t), p_j + f(j−1, t−a′_j)}, capped at d_j
-- statement:
--   Let $n$ jobs have nonnegative integer processing times $a'_j$, nonnegative integer deadlines $d_j$ and real weights $p_j$. Equation (3) of Lawler and Moore defines, for $j = 0, 1, \dots, n$ and integer $t$, a value $f(j, t) \in \mathbb R \cup \{-\infty\}$ by
--   $$
--   f(0, t) = 0 \ (t \ge 0), \qquad f(j, t) = -\infty \ (t < 0),
--   $$
--   and, for $j = 1, \dots, n$ and $t \ge 0$,
--   $$
--   f(j, t) = \begin{cases} \max\{f(j, t-1),\ f(j-1, t),\ p_j + f(j-1, t - a'_j)\}, & t \le d_j,\\ f(j, d_j), & t > d_j. \end{cases}
--   $$
--   Here $p_j + (-\infty) = -\infty$.
--
--   The value $f(j, t)$ is meant to be the largest total weight of on-time jobs among the first $j$ jobs when the on-time jobs among them finish by time $t$; Section 6 uses $f$ to solve the weighted-tardy-jobs problem.
--
--   **Formalization Note** The paper prints (3) without base cases; they are taken from Equation (1) (p. 77), with $+\infty$ replaced by $-\infty$ because (3) is a maximum. The value lives in `WithBot ℝ` ($\bot = -\infty$). The term $f(j, t-1)$, which the paper notes is dominated, is kept as printed. The paper's job $j$ is Lean job `⟨j - 1, _⟩`, so the cap compares $t$ with `d ⟨j - 1, _⟩`. For $j > n$ (no such job) Lean sets $f(j, t) = f(j-1, t)$; this case is never used.
-- source:
--   Lawler, Moore, A Functional Equation and Its Application to Resource Allocation and Sequencing Problems, Management Sci. 16 (1969), p. 80, Eq. (3) (base cases from Eq. (1), p. 77)

import Mathlib

namespace LawlerMoore.WeightedTardy

/-- The function `f(j, t)` of Equation (3) (Lawler–Moore 1969, §6, p. 80), as printed:
for the paper's job `j ≥ 1` (Lean job `⟨j - 1, _⟩`) and `0 ≤ t`,
`f(j, t) = max{f(j, t - 1), f(j - 1, t), p_j + f(j - 1, t - a'_j)}` if `t ≤ d_j`, and
`f(j, t) = f(j, d_j)` if `t > d_j`.
The base cases, not printed with (3), are those of Equation (1) (p. 77) with `+∞` replaced by
`-∞` for a maximum: `f(0, t) = 0` for `t ≥ 0` and `f(j, t) = -∞` (`⊥`) for `t < 0`.
For `j > n` (no such job) the value is `f(j - 1, t)`; this case is never used. -/
noncomputable def eq3 {n : ℕ} (a' d : Fin n → ℕ) (p : Fin n → ℝ) : ℕ → ℤ → WithBot ℝ
  | 0, t => if 0 ≤ t then 0 else ⊥
  | j + 1, t =>
    if ht : t < 0 then ⊥
    else if h : j < n then
      if htd : t ≤ (d ⟨j, h⟩ : ℤ) then
        max (max (eq3 a' d p (j + 1) (t - 1)) (eq3 a' d p j t))
          ((p ⟨j, h⟩ : WithBot ℝ) + eq3 a' d p j (t - (a' ⟨j, h⟩ : ℤ)))
      else eq3 a' d p (j + 1) (d ⟨j, h⟩ : ℤ)
    else eq3 a' d p j t
termination_by j t => (j, (t + 1).toNat)
decreasing_by
  all_goals first
    | exact Prod.Lex.left _ _ (by omega)
    | exact Prod.Lex.right _ (by omega)

end LawlerMoore.WeightedTardy


