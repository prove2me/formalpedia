-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_ReducedBoundaryCost
-- name    : DiscreteConvex_NetworkFlowsB_ReducedBoundaryCost
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:21:19.847227+00:00
-- url     : https://prove2.me/theorems/c23d9e74-d533-4a1c-843e-f8ac665f9bed
-- title:
--   ReducedBoundaryCost
-- statement:
--   The reduced boundary cost $f[-p](x)=f(x)-\sum_v p(v)x(v)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.249, Eq. (9.23).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.249, Eq. (9.23)

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The reduced boundary cost `f[−p](x) = f(x) − Σ p(v)x(v)`. -/
def ReducedBoundaryCost (f : (V → ℝ) → WithTop ℝ) (p : V → ℝ) (x : V → ℝ) : WithTop ℝ :=
  f x - ((∑ v, p v * x v : ℝ) : WithTop ℝ)

end DiscreteConvex.NetworkFlowsB


