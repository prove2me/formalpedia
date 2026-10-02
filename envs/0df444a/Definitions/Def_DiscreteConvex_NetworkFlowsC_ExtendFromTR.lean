-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_ExtendFromTR
-- name    : DiscreteConvex_NetworkFlowsC_ExtendFromTR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:49:26.546023+00:00
-- url     : https://prove2.me/theorems/858bcf7b-4503-45bf-a293-084da4a9f789
-- title:
--   Extension of a real vector on T by zero
-- statement:
--   The vector of $\mathbb{R}^V$ extending $y\in\mathbb{R}^T$ by zero outside $T$; the real-domain counterpart.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §9.6.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §9.6

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vector of `Rⱽ` extending `y ∈ Rᵀ` by zero outside `T`; the real-domain counterpart of
`ExtendFromT`. -/
def ExtendFromTR (T : Finset V) (y : {v // v ∈ T} → ℝ) : V → ℝ :=
  fun v => if h : v ∈ T then y ⟨v, h⟩ else 0

end DiscreteConvex.NetworkFlowsC


