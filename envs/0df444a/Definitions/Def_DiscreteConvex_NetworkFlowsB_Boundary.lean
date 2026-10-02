-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_Boundary
-- name    : DiscreteConvex_NetworkFlowsB_Boundary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:20:40.294281+00:00
-- url     : https://prove2.me/theorems/df801608-d519-4e70-b4d8-537f54b708ad
-- title:
--   Boundary
-- statement:
--   The boundary $\partial\xi(v)=\sum_{a\in\delta^+v}\xi(a)-\sum_{a\in\delta^-v}\xi(a)$ of a real flow.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.245, Eq. (9.1).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.245, Eq. (9.1)

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The **boundary** `∂ξ(v) = Σ{ξ(a) : a ∈ δ⁺v} − Σ{ξ(a) : a ∈ δ⁻v}` of a real flow, `tail = ∂⁺`,
`head = ∂⁻`. -/
def Boundary (tail head : A → V) (xi : A → ℝ) (v : V) : ℝ :=
  (∑ a ∈ Finset.univ.filter (fun a => tail a = v), xi a) -
    (∑ a ∈ Finset.univ.filter (fun a => head a = v), xi a)

end DiscreteConvex.NetworkFlowsB


