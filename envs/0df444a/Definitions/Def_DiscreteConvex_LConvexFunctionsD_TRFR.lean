-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_TRFR
-- name    : DiscreteConvex_LConvexFunctionsD_TRFR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:59:11.122604+00:00
-- url     : https://prove2.me/theorems/7cdfd0df-f372-4a72-95cb-2e97a987fcdc
-- title:
--   TRFR
-- statement:
--   Axiom (TRF[R]): $\exists r$, $g(p+\alpha\mathbf 1)=g(p)+\alpha r$ for all $p\in\mathbb R^V,\alpha\in\mathbb R$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.190, axiom (TRF[R]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.190, axiom (TRF[R])

import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (TRF[R]): `∃r, g(p+α1) = g(p)+αr` for all `p ∈ Rⱽ, α ∈ R`. -/
def TRFR (g : (V → ℝ) → WithTop ℝ) : Prop :=
  ∃ r : ℝ, ∀ p : V → ℝ, ∀ alpha : ℝ, g (fun v => p v + alpha) = g p + (alpha * r : WithTop ℝ)

end DiscreteConvex.LConvexFunctionsD


