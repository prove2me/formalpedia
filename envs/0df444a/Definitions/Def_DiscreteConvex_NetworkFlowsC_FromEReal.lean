-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_FromEReal
-- name    : DiscreteConvex_NetworkFlowsC_FromEReal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:48:11.768989+00:00
-- url     : https://prove2.me/theorems/793ae8c6-5412-4ead-96fd-d37f6a0b1819
-- title:
--   FromEReal
-- statement:
--   The projection $\mathbb R\cup\{\pm\infty\}\to\mathbb R\cup\{+\infty\}$ sending $-\infty$ to the junk value $+\infty$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, Eq. (8.11), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, Eq. (8.11), redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def FromEReal (v : EReal) : WithTop ℝ := WithBot.unbotD ⊤ v

end DiscreteConvex.NetworkFlowsC


