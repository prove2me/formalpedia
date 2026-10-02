-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_Coboundary
-- name    : DiscreteConvex_NetworkFlowsB_Coboundary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:20:43.75124+00:00
-- url     : https://prove2.me/theorems/5bcddfbc-c9e7-4c41-b05f-2a3858ec5e8c
-- title:
--   Coboundary
-- statement:
--   The coboundary $\delta p(a)=p(\partial^+a)-p(\partial^-a)$ of a potential.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.249, Eq. (9.20).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.249, Eq. (9.20)

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The coboundary `δp(a) = p(∂⁺a) − p(∂⁻a)` of a potential `p : V → R`. -/
def Coboundary (tail head : A → V) (p : V → ℝ) (a : A) : ℝ := p (tail a) - p (head a)

end DiscreteConvex.NetworkFlowsB


