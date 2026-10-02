-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_TRF
-- name    : DiscreteConvex_LConvexFunctionsD_TRF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:59:00.249008+00:00
-- url     : https://prove2.me/theorems/20fcd98a-b39a-4274-8388-7fcfcf786b03
-- title:
--   TRF
-- statement:
--   Axiom (TRF[Z]): $\exists r$, $g(p+\mathbf 1)=g(p)+r$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (TRF[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (TRF[Z])

import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (TRF[Z]): `∃r, g(p+1) = g(p)+r`. -/
def TRF (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∃ r : ℝ, ∀ p : V → ℤ, g (p + 1) = g p + (r : WithTop ℝ)

end DiscreteConvex.LConvexFunctionsD


