-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_ReducedArcCost
-- name    : DiscreteConvex_NetworkFlowsB_ReducedArcCost
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:23:34.833648+00:00
-- url     : https://prove2.me/theorems/c0e6fa0d-3c68-4fc6-8688-2322ea05ae6a
-- title:
--   ReducedArcCost
-- statement:
--   The reduced arc cost $f_a[\delta p(a)](t)=f_a(t)+\delta p(a)\cdot t$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.249, Eq. (9.24).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.249, Eq. (9.24)

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_Coboundary

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The reduced arc cost `fa[δp(a)](t) = fa(t) + δp(a)·t`. -/
def ReducedArcCost (tail head : A → V) (fa : A → ℝ → WithTop ℝ) (p : V → ℝ) (a : A) (t : ℝ) :
    WithTop ℝ :=
  fa a t + ((Coboundary tail head p a * t : ℝ) : WithTop ℝ)

end DiscreteConvex.NetworkFlowsB


