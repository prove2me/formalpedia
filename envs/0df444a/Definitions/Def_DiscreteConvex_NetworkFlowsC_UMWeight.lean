-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_UMWeight
-- name    : DiscreteConvex_NetworkFlowsC_UMWeight
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:53:47.776741+00:00
-- url     : https://prove2.me/theorems/c75b6105-15af-4b79-97f5-a4f8dc1a8fa3
-- title:
--   UMWeight
-- statement:
--   The weight function $c(u,v)=\Delta f(x;v,u)$ on $E$, $+\infty$ off it.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.266, preceding Prop. 9.23.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.266, preceding Prop. 9.23

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_DomZ
import Definitions.Def_DiscreteConvex_NetworkFlowsC_DeltaF

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The weight function `c(u,v) = Δf(x;v,u)` on `E`, `+∞` off it. -/
noncomputable def UMWeight (f : (V → ℤ) → WithTop ℝ) (x : V → ℤ) (u v : V) : WithTop ℝ :=
  if (fun w => x w - (if w = u then (1:ℤ) else 0) + (if w = v then (1:ℤ) else 0)) ∈ DomZ f then
    DeltaF f x v u
  else ⊤

end DiscreteConvex.NetworkFlowsC


