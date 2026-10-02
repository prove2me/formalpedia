-- Prove2me | Definitions.Def_AppliedComb_GenFun_binomReal
-- name    : AppliedComb_GenFun_binomReal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:11:07.296931+00:00
-- url     : https://prove2.me/theorems/5b4688cf-8f0d-46ce-9bf2-020e49f65136
-- title:
--   Definitions 8.8–8.9 — P(p, k) and the generalized binomial coefficient C(p, k) for real p
-- statement:
--   For every real number $p$ and every nonnegative integer $k$, the number $P(p, k)$ is defined recursively by
--
--   1. $P(p, 0) = 1$ for all real numbers $p$, and
--   2. $P(p, k) = p \cdot P(p - 1, k - 1)$ for all real numbers $p$ and integers $k > 0$.
--
--   Unwinding the recursion, $P(p, k) = p(p-1)(p-2)\cdots(p-k+1)$, a product of $k$ factors; no condition $p \ge k$ is imposed, so for instance $P(-5, 4) = (-5)(-6)(-7)(-8)$. The **generalized binomial coefficient** is then
--
--   $$\binom{p}{k} = C(p, k) = \frac{P(p, k)}{k!}.$$
--
--   For integers $0 \le p < k$ one gets $P(p, k) = C(p, k) = 0$, and for integers $p \ge k \ge 0$ the ordinary binomial coefficient. These numbers are the coefficients in Newton's Binomial Theorem for a real exponent.
--
--   **Formalization Note.** `fallingP p k` is $P(p, k)$, defined by structural recursion on $k$ exactly as in Definition 8.8 (the step case $k+1$ gives `p * fallingP (p - 1) k`). `binomReal p k` is $C(p, k)$ = `fallingP p k / k!` in $\mathbb{R}$; since $k! \ne 0$ the division is never degenerate. Mathlib's `descPochhammer` and `Ring.choose` compute the same numbers, but the book's own recursion is used so that Lemma 8.11 is a statement about it.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 166, Definitions 8.8 and 8.9

import Mathlib

namespace AppliedComb.GenFun

/-- Keller–Trotter, Definition 8.8 (p. 166). For every real number `p` and nonnegative integer
`k`, the number `P(p, k)` is defined by
1. `P(p, 0) = 1` for all real numbers `p`, and
2. `P(p, k) = p · P(p - 1, k - 1)` for all real numbers `p` and integers `k > 0`.
No condition `p ≥ k` is imposed. -/
def fallingP : ℝ → ℕ → ℝ
  | _, 0 => 1
  | p, k + 1 => p * fallingP (p - 1) k

/-- Keller–Trotter, Definition 8.9 (p. 166). For every real number `p` and nonnegative integer
`k`, the generalized binomial coefficient is `C(p, k) = P(p, k) / k!`, with `P` the number
`fallingP` of Definition 8.8. -/
noncomputable def binomReal (p : ℝ) (k : ℕ) : ℝ :=
  fallingP p k / (Nat.factorial k : ℝ)

end AppliedComb.GenFun


