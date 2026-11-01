-- Prove2me | Definitions.Def_LocalDOvS_SUS_interp
-- name    : LocalDOvS_SUS_interp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:24:13.61841+00:00
-- url     : https://prove2.me/theorems/163deaf3-06a2-4b07-bb3c-130781210996
-- title:
--   Linear interpolation $\tilde f$ of eq. (2)
-- statement:
--   For a function $f$ on the integers, its **linear interpolation** is the real function
--
--   $$
--   \tilde f(x) := [f(x_0+1)-f(x_0)]\,(x-x_0)+f(x_0),\qquad x\in[x_0,x_0+1],
--   $$
--
--   with $x_0=\lfloor x\rfloor$. On $[1,N]$ this is the function of eq. (2) of the paper: on each piece $[x_0,x_0+1]$, $x_0\in[N-1]$, it is the chord between $(x_0,f(x_0))$ and $(x_0+1,f(x_0+1))$; two adjacent pieces agree at the integer they share. It reduces statements about minima of $f$ over integer intervals to minima of a convex function over real intervals.
--
--   **Formalization Note** The piece is selected by $\lfloor x\rfloor$, so at an integer $x$ the formula reads $f(x)$; values outside $[1,N]$ are never used.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, §3, eq. (2), p.11

import Mathlib

namespace LocalDOvS.SUS

/-- The linear interpolation `f̃` of a function `f` on the integers (Zhang–Zheng–Lavaei,
arXiv:2012.02427v2, §3, eq. (2), p.11):
`f̃(x) := [f(x₀ + 1) − f(x₀)] · (x − x₀) + f(x₀)` for `x ∈ [x₀, x₀ + 1]`, `x₀ ∈ [N − 1]`.

**Formalization Note.** The piece is selected by `x₀ := ⌊x⌋₊`. At an integer `x = x₀ + 1` the
two adjacent pieces of (2) agree (both give `f(x₀ + 1)`), so this choice is the paper's function
on `[1, N]`; at `x = N` the formula reads `f(N)`. Outside `[1, N]` the value is irrelevant. -/
noncomputable def interp (f : ℕ → ℝ) (x : ℝ) : ℝ :=
  (f (⌊x⌋₊ + 1) - f ⌊x⌋₊) * (x - ⌊x⌋₊) + f ⌊x⌋₊

end LocalDOvS.SUS


