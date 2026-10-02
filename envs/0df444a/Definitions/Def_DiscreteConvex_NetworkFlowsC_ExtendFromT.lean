-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_ExtendFromT
-- name    : DiscreteConvex_NetworkFlowsC_ExtendFromT
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:49:12.626996+00:00
-- url     : https://prove2.me/theorems/3875e559-9ba2-4bae-b49b-c406105d3227
-- title:
--   Extension of a vector on T by zero
-- statement:
--   The vector of $\mathbb{Z}^V$ extending $y\in\mathbb{Z}^T$ by zero outside $T$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §9.6, Eq. (9.81).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §9.6, Eq. (9.81)

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vector of `Zⱽ` extending `y ∈ Zᵀ` by zero outside `T`. The induced functions `f̃` and `g̃`
of Eqs. (9.81) and (9.82) are the book's functions **on `Zᵀ`**; read on all of `Zⱽ` they are
cylinders along `V ∖ T`, and the exchange axiom then fails whenever `T ≠ V` (comparing `y` with
`y + χw` for `w ∉ T` leaves the negative support empty). -/
def ExtendFromT (T : Finset V) (y : {v // v ∈ T} → ℤ) : V → ℤ :=
  fun v => if h : v ∈ T then y ⟨v, h⟩ else 0

end DiscreteConvex.NetworkFlowsC


