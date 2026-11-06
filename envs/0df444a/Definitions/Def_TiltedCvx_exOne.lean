-- Prove2me | Definitions.Def_TiltedCvx_exOne
-- name    : TiltedCvx_exOne
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:17.127741+00:00
-- url     : https://prove2.me/theorems/1b7597b6-f58b-4a31-9268-d4b155d8ed9f
-- title:
--   The function of Example 1
-- statement:
--   For $\gamma\in(0,1)$, the function $f:\mathbb R\to\overline{\mathbb R}$ of Example 1 is
--
--   $$
--   f(x):=\begin{cases}x, & -1\le x\le0,\\ \gamma x, & 0\le x\le1,\\ +\infty, & x\notin[-1,1].\end{cases}
--   $$
--
--   Its slope drops by the factor $\gamma$ at $0$; it has all three optimal parameters equal to $\gamma$.
--
--   **Formalization Note** The two formulas agree at $x=0$.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Example 1, p.29

import Mathlib

namespace TiltedCvx

/-- **The function of Example 1.** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, Example 1,
p.29: for `γ ∈ (0, 1)`, `f(x) := x` for `−1 ≤ x ≤ 0`, `γx` for `0 ≤ x ≤ 1`, and `+∞` for
`x ∉ [−1, 1]`.

**Formalization Note** A function `ℝ → EReal`. The two formulas agree at `x = 0`; the first
branch is taken there. -/
noncomputable def exOne (γ : ℝ) (x : ℝ) : EReal :=
  if -1 ≤ x ∧ x ≤ 0 then ((x : ℝ) : EReal)
  else if 0 ≤ x ∧ x ≤ 1 then ((γ * x : ℝ) : EReal) else ⊤

end TiltedCvx


