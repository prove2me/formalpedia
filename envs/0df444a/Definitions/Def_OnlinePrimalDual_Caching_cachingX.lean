-- Prove2me | Definitions.Def_OnlinePrimalDual_Caching_cachingX
-- name    : OnlinePrimalDual_Caching_cachingX
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:46:01.405854+00:00
-- url     : https://prove2.me/theorems/b4e2cdfe-8a63-4e8d-abe3-719cf893782a
-- title:
--   The Fractional Caching algorithm's final primal value
-- statement:
--   Step (3) of the Fractional Caching algorithm (p. 154) sets `x(p,j) ← 1/k` exactly when
--   `(∑_{t|v∈S t} y t) − z(p,j)` first reaches `c(p,j)`; step (4) then continuously updates
--   `x(p,j)` (while `1/k ≤ x(p,j) < 1`) via `x(p,j) ← (1/k)exp((1/cp)[(∑ y t) − z(p,j) − cp])`.
--   Evaluating this closed form at the algorithm's final accumulated dual values, capped at `1`
--   (matching the book's own proof, p. 155, that each `x(p,j)` "is never increased to be greater
--   than 1"), reproduces the algorithm's final value including its freeze once `x(p,j) = 1`.
--   Before activation, `x(p,j) = 0`.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 153-155, Fractional Caching algorithm, steps (3)-(4)

import Mathlib
import Definitions.Def_OnlinePrimalDual_Caching_CachingInstance
import Definitions.Def_OnlinePrimalDual_Caching_dualSum

namespace OnlinePrimalDual.Caching

/-- The final value the Fractional Caching algorithm (p. 153-154, PDF p. 64-65) assigns to primal
variable `v = (p,j)`. Step (3) sets `x(p,j) ← 1/k` exactly when `(∑_{t|v∈S t} y t) − z(p,j)` first
reaches `c(p,j)`; step (4) then continuously updates `x(p,j)` (while `1/k ≤ x(p,j) < 1`) by
`x(p,j) ← (1/k) exp((1/cp)[(∑ y t) − z(p,j) − cp])`. Since `z(p,j)` only ever increases (at the
same rate as `y`) once `x(p,j)` reaches `1` — before that `z(p,j) = 0` — the quantity
`dualSum inst y v − z v` is monotone non-decreasing throughout the run, and this closed form is
monotone non-decreasing in that quantity; evaluating it at the *final* accumulated values and
capping at `1` (`min 1 …`) therefore reproduces the same final value as the step-by-step process,
including its freeze once `x(p,j) = 1` (the book's own proof uses exactly this freeze fact, p. 155:
"the value of x(p,j) is not going to change anymore"). Before activation
(`dualSum inst y v − z v < c v`), the variable has not yet been touched by step (3) and is `0`. -/
noncomputable def cachingX {V Time : Type*} [Fintype V] [Fintype Time] [DecidableEq V]
    (inst : CachingInstance V Time) (y : Time → ℝ) (z : V → ℝ) (v : V) : ℝ :=
  if dualSum inst y v - z v < inst.c v then 0
  else min 1 ((1 / (inst.k : ℝ)) * Real.exp ((dualSum inst y v - z v - inst.c v) / inst.c v))

end OnlinePrimalDual.Caching


