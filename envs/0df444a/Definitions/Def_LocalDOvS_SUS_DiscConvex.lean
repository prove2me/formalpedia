-- Prove2me | Definitions.Def_LocalDOvS_SUS_DiscConvex
-- name    : LocalDOvS_SUS_DiscConvex
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:24:04.501642+00:00
-- url     : https://prove2.me/theorems/d2595927-f4d4-4bbf-b63f-b2861a563d80
-- title:
--   Discrete convexity on $[N]$
-- statement:
--   A function $f$ on the integers is **discretely convex on** $[N]=\{1,\dots,N\}$ if it satisfies the discrete midpoint convexity property
--
--   $$
--   f(x+1)+f(x-1)\ge 2f(x)\qquad\text{for all }x\in\{2,\dots,N-1\}.
--   $$
--
--   This is the paper's notion of convexity of the objective on the one-dimensional decision space (Assumption 1 for $d=1$); equivalently, the increments $f(x+1)-f(x)$ are nondecreasing on $[N]$.
--
--   **Formalization Note** $f$ is a function on $\mathbb N$; only its values on $[N]$ enter. The range is written $2\le x$, $x+1\le N$.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, §3, p.11 (Assumption 1, p.8)

import Mathlib

namespace LocalDOvS.SUS

/-- Discrete convexity of `f` on `[N] = {1, …, N}` (Zhang–Zheng–Lavaei, arXiv:2012.02427v2, §3,
p.11, Assumption 1 in dimension one): the discrete midpoint convexity property
`f(x + 1) + f(x − 1) ≥ 2 f(x)` for all `x ∈ {2, …, N − 1}`.

**Formalization Note.** Points are natural numbers; only the values of `f` on `{1, …, N}` enter.
The range `x ∈ {2, …, N − 1}` is written `2 ≤ x` and `x + 1 ≤ N`, so no natural-number
subtraction occurs in the range (and `x − 1 ≥ 1` inside it). -/
def DiscConvex (N : ℕ) (f : ℕ → ℝ) : Prop :=
  ∀ x : ℕ, 2 ≤ x → x + 1 ≤ N → 2 * f x ≤ f (x + 1) + f (x - 1)

end LocalDOvS.SUS


