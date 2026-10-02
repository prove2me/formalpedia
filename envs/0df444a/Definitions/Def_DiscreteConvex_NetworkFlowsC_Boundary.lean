-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_Boundary
-- name    : DiscreteConvex_NetworkFlowsC_Boundary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:47:24.070856+00:00
-- url     : https://prove2.me/theorems/ddebbd9a-c06b-4e85-8ea2-4316fa31aef3
-- title:
--   Boundary
-- statement:
--   The boundary $\partial\xi(v)=\sum_{a\in\delta^+v}\xi(a)-\sum_{a\in\delta^-v}\xi(a)$ of a real flow.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.245, Eq. (9.1), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.245, Eq. (9.1), redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def Boundary (tail head : A → V) (xi : A → ℝ) (v : V) : ℝ :=
  (∑ a ∈ Finset.univ.filter (fun a => tail a = v), xi a) -
    (∑ a ∈ Finset.univ.filter (fun a => head a = v), xi a)

end DiscreteConvex.NetworkFlowsC


