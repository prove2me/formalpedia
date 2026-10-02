-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_DiscreteConvexArcZ
-- name    : DiscreteConvex_NetworkFlowsB_DiscreteConvexArcZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:21:02.039505+00:00
-- url     : https://prove2.me/theorems/e1c86502-eab7-4a9c-9639-57ce019e0fd5
-- title:
--   Discrete convexity of a univariate arc cost
-- statement:
--   A univariate arc cost $\psi:\mathbb{Z}\to\mathbb{R}\cup\{+\infty\}$ is discrete convex (the book's class $C[\mathbb{Z}\to\mathbb{R}]$): its effective domain is nonempty and $\psi(t)+\psi(t+2)\ge 2\psi(t+1)$ for every $t$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §9.3, Theorem 9.16.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §9.3, Theorem 9.16

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

/-- A univariate arc cost `ψ : Z → R∪{+∞}` is discrete convex (the book's class `C[Z→R]`).
Theorem 9.16 assumes each `fa` lies in it; without the assumption the potential criterion fails
(one arc, `f` the indicator of `0`, `fa(t) = -t²`: the zero flow is optimal but no potential puts
`0` in `arg min (fa + δp)`). -/
def DiscreteConvexArcZ (psi : ℤ → WithTop ℝ) : Prop :=
  (∃ x, psi x ≠ ⊤) ∧ ∀ x : ℤ, psi x + psi (x + 2) ≥ psi (x + 1) + psi (x + 1)

end DiscreteConvex.NetworkFlowsB


