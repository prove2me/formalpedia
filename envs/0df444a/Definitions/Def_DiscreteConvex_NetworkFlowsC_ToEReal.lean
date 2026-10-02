-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_ToEReal
-- name    : DiscreteConvex_NetworkFlowsC_ToEReal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:48:13.999087+00:00
-- url     : https://prove2.me/theorems/b9565c39-21a4-499a-bcd8-7f40cbf9d9d5
-- title:
--   ToEReal
-- statement:
--   The canonical embedding $\mathbb R\cup\{+\infty\}\hookrightarrow\mathbb R\cup\{\pm\infty\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, Eq. (8.11), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, Eq. (8.11), redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def ToEReal (v : WithTop ℝ) : EReal := WithBot.some v

end DiscreteConvex.NetworkFlowsC


