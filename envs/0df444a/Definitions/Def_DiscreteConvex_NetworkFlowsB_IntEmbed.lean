-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_IntEmbed
-- name    : DiscreteConvex_NetworkFlowsB_IntEmbed
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:21:07.757469+00:00
-- url     : https://prove2.me/theorems/0f7037cd-0878-427a-9d50-8724b3917f17
-- title:
--   IntEmbed
-- statement:
--   The real embedding of a set of integer vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.107, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.107, redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The real embedding of a set of integer vectors. -/
def IntEmbed (B : Set (V → ℤ)) : Set (V → ℝ) := (fun x : V → ℤ => fun v => (x v : ℝ)) '' B

end DiscreteConvex.NetworkFlowsB


