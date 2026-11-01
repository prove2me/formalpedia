-- Prove2me | Definitions.Def_LocalDOvS_SUS_SUSState
-- name    : LocalDOvS_SUS_SUSState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:24:08.044102+00:00
-- url     : https://prove2.me/theorems/fe7307af-a820-4c83-a90f-818d9302aab7
-- title:
--   State of the shrinking uniform sampling algorithm
-- statement:
--   The state of the shrinking uniform sampling algorithm at the beginning of its $k$-th iteration: the iteration index $k$; the active set $S_k=\{x_0,x_0+s,\dots,x_0+(M-1)s\}$, given by its minimum $x_0$, the step size $s=d_k$ and its size $M$; the bounds $x_{L,k}$ and $x_{U,k}$ of the proof (p.ec14), which the algorithm does not use; and the number of simulations of each decision required so far, which determines exactly which outputs the algorithm has seen.
--
--   **Formalization Note** Every active set of Algorithm 2 is an arithmetic progression of this form: $S_1=[N]$, a Type-I Operation keeps an initial or final segment and a Type-II Operation keeps every other point.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, Algorithm 2, p.15; p.ec14

import Mathlib

namespace LocalDOvS.SUS

/-- The state of the corrected shrinking uniform sampling algorithm at the beginning of its
`k`-th iteration (Zhang–Zheng–Lavaei, arXiv:2012.02427v2, Algorithm 2, p.15, and the notation
`S_k`, `d_k`, `x_{L,k}`, `x_{U,k}` of p.ec14). The active set is the progression
`S_k = {x0, x0 + s, …, x0 + (M − 1)s}` (see `actSet`).

**Formalization Note.** Every active set of Algorithm 2 is such a progression: `S_1 = [N]`,
Type-I Operations keep an initial or final segment, Type-II Operations keep every other point
(this is checked in `Solutions/verification`). `xL`, `xU` are the bounds of p.ec14, which the
algorithm does not use; `cnt x` is the number of simulations of `x` that the algorithm has
required so far, which determines exactly which outputs the algorithm has seen. -/
structure SUSState where
  /-- The iteration index `k` (starting at `1`). -/
  k : ℕ
  /-- `min S_k`. -/
  x0 : ℕ
  /-- The step size `d_k`. -/
  s : ℕ
  /-- `|S_k|`. -/
  M : ℕ
  /-- The lower bound `x_{L,k}` of p.ec14 (corrected). -/
  xL : ℕ
  /-- The upper bound `x_{U,k}` of p.ec14 (corrected). -/
  xU : ℕ
  /-- The number of simulations of each decision required so far. -/
  cnt : ℕ → ℕ

end LocalDOvS.SUS


