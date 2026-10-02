-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_SupportedOnR
-- name    : DiscreteConvex_NetworkFlowsC_SupportedOnR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:49:21.751834+00:00
-- url     : https://prove2.me/theorems/6101b31c-45b0-4556-b760-7c2c528f951f
-- title:
--   SupportedOnR
-- statement:
--   $x$ is supported on $S$, real version.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.271, real version.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.271, real version

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def SupportedOnR (S : Finset V) (x : V → ℝ) : Prop := ∀ v, v ∉ S → x v = 0

end DiscreteConvex.NetworkFlowsC


