-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_SupportedOn
-- name    : DiscreteConvex_NetworkFlowsC_SupportedOn
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:49:13.793229+00:00
-- url     : https://prove2.me/theorems/88549ee5-f03a-43e4-a2a1-7e594342ae76
-- title:
--   SupportedOn
-- statement:
--   $x$ is supported on $S$: $x(v)=0$ for $v\notin S$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.269, Eq. (9.81)-adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.269, Eq. (9.81)-adjacent

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- `x` is supported on `S`: `x(v) = 0` for `v ∉ S`. -/
def SupportedOn (S : Finset V) (x : V → ℤ) : Prop := ∀ v, v ∉ S → x v = 0

end DiscreteConvex.NetworkFlowsC


