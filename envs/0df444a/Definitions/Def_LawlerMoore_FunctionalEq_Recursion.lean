-- Prove2me | Definitions.Def_LawlerMoore_FunctionalEq_Recursion
-- name    : LawlerMoore_FunctionalEq_Recursion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:42:35.646606+00:00
-- url     : https://prove2.me/theorems/ccd62053-d275-4b39-8927-5664771bcfe4
-- title:
--   Eq. (1) — the functional equation f(j, t) = min{f(j, t−1), α_j(t) + f(j−1, t−a_j), β_j(t) + f(j−1, t−b_j)}
-- statement:
--   For the two-mode problem with processing times $a_j, b_j \in \mathbb N$ and losses $\alpha_j, \beta_j$, define $f(j, t) \in \mathbb R \cup \{+\infty\}$ for $j = 0, 1, \dots, n$ and integers $t$ by
--   $$f(0, t) = 0 \quad (t \ge 0), \qquad f(j, t) = +\infty \quad (t < 0),$$
--   $$f(j, t) = \min\bigl\{\, f(j, t-1),\ \alpha_j(t) + f(j-1, t-a_j),\ \beta_j(t) + f(j-1, t-b_j) \,\bigr\} \qquad (j = 1, \dots, n;\ t \ge 0).$$
--   This is the paper's Eq. (1), taken exactly as printed; the convention $x + (+\infty) = +\infty$ applies.
--
--   The recursion is the paper's computational device: it is a knapsack-like equation in which the term $f(j, t-1)$ lets job $j$ finish before $t$, and the other two terms let it finish exactly at $t$ in one of the two modes.
--
--   **Formalization Note** The values live in `WithTop ℝ`, with `⊤` for $+\infty$. Lean job `⟨j, _⟩` is the paper's job $j+1$, so `f (j+1)` uses `α ⟨j,_⟩`, `a ⟨j,_⟩`. Losses are evaluated at `t.toNat`, which is $t$ because the case $t < 0$ is handled first. The paper defines $f$ only for $j \le n$; for $j > n$ the Lean value is `⊤` and is never used. The definition is by well-founded recursion on $(j, t+1)$.
-- source:
--   Lawler, Moore, A Functional Equation and Its Application to Resource Allocation and Sequencing Problems, Management Sci. 16 (1969), p. 77, Eq. (1)

import Mathlib

namespace LawlerMoore.FunctionalEq

/-- The function `f(j, t)` of Eq. (1) (Lawler and Moore 1969, p. 77), with values in
`WithTop ℝ` (`⊤` is the paper's `+∞`, and `↑x + ⊤ = ⊤`):

* `f(j, t) = +∞` for `t < 0`;
* `f(0, t) = 0` for `t ≥ 0`;
* `f(j, t) = min {f(j, t − 1), α_j(t) + f(j − 1, t − a_j), β_j(t) + f(j − 1, t − b_j)}`
  for `j = 1, …, n` and `t ≥ 0`.

The paper's job `j` is Lean job `⟨j - 1, _⟩`, so `f (j + 1)` uses `α ⟨j, _⟩`, `a ⟨j, _⟩`.
Losses are evaluated at `t.toNat`, which equals `t` under the guard `0 ≤ t`. For `j > n` the
paper does not define `f`; here `f j t = ⊤` there, a value never used. The recursion is
well founded on `(j, (t + 1).toNat)` lexicographically. -/
def f {n : ℕ} (a b : Fin n → ℕ) (α β : Fin n → ℕ → ℝ) : ℕ → ℤ → WithTop ℝ
  | j, t =>
    if _ht : t < 0 then ⊤
    else
      match j with
      | 0 => 0
      | j + 1 =>
        if hj : j < n then
          min (f a b α β (j + 1) (t - 1))
            (min ((α ⟨j, hj⟩ t.toNat : WithTop ℝ) + f a b α β j (t - (a ⟨j, hj⟩ : ℤ)))
              ((β ⟨j, hj⟩ t.toNat : WithTop ℝ) + f a b α β j (t - (b ⟨j, hj⟩ : ℤ))))
        else ⊤
termination_by j t => (j, (t + 1).toNat)
decreasing_by
  all_goals first
    | (apply Prod.Lex.right; omega)
    | (apply Prod.Lex.left; omega)

end LawlerMoore.FunctionalEq


