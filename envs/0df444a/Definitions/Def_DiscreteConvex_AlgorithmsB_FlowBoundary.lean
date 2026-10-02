-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_FlowBoundary
-- name    : DiscreteConvex_AlgorithmsB_FlowBoundary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:51:13.899833+00:00
-- url     : https://prove2.me/theorems/5088f26a-44c3-4405-af2d-f87d62d45e80
-- title:
--   FlowBoundary
-- statement:
--   $\partial\phi(v)=\sum_u\phi(v,u)-\sum_u\phi(u,v)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.296, adjacent to Eq. (10.21).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.296, adjacent to Eq. (10.21)

import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `∂ϕ(v) = Σ_u ϕ(v,u) - Σ_u ϕ(u,v)`. -/
def FlowBoundary (phi : V → V → ℝ) (v : V) : ℝ := (∑ u, phi v u) - (∑ u, phi u v)

end DiscreteConvex.AlgorithmsB


