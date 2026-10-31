-- Prove2me | Definitions.Def_ApproxVI_segIdx
-- name    : ApproxVI_segIdx
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:14:19.417004+00:00
-- url     : https://prove2.me/theorems/b3b48f3e-5bcc-4fc4-a759-c5e66c6de614
-- title:
--   The index $n$ with $t\in[t_n,t_{n+1})$
-- statement:
--   For $t\ge0$, the interval index of $t$ is the least $n$ with $t<t_{n+1}$. When every $a(n)>0$ and $\sum_n a(n)=\infty$, the intervals $[t_n,t_{n+1})$ partition $[0,\infty)$ and this is the unique $n$ with $t_n\le t<t_{n+1}$.
--
--   It is used to define the piecewise trajectories $X_l$, $Y_c$, $G_c$ and $W_l$ of §6.1.
--
--   **Formalization Note** Outside the regime $a(n)>0$, $\sum a(n)=\infty$, $t\ge0$ the value is the convention $0$; no statement relies on it.
-- source:
--   Ramaswamy & Bhatnagar, Analyzing Approximate Value Iteration Algorithms, arXiv:1709.04673v5, §6.1, (20), p.22

import Mathlib
import Definitions.Def_ApproxVI_tSeq

namespace ApproxVI

/-- The index `n` of the interval `[tₙ, tₙ₊₁)` containing `t`, used to define the piecewise
trajectories of Ramaswamy & Bhatnagar, *Analyzing Approximate Value Iteration Algorithms*,
arXiv:1709.04673v5, §6.1, (20), p.22: the least `n` with `t < tₙ₊₁`.

**Formalization Note** When every `a(n) > 0` and `Σ a(n) = ∞` (the standing assumptions of
§6), the intervals `[tₙ, tₙ₊₁)` partition `[0, ∞)`, and for `t ≥ 0` this is the unique `n`
with `tₙ ≤ t < tₙ₊₁`. Outside that regime (or for `t < 0`) the value is a convention
(`sInf ∅ = 0` in `ℕ`) that no statement relies on. -/
noncomputable def segIdx (a : ℕ → ℝ) (t : ℝ) : ℕ :=
  sInf {n : ℕ | t < tSeq a (n + 1)}

end ApproxVI


