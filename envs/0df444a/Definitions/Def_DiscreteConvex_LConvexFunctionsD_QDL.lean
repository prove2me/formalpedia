-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_QDL
-- name    : DiscreteConvex_LConvexFunctionsD_QDL
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:59:54.384983+00:00
-- url     : https://prove2.me/theorems/0fee7236-78b5-40e8-915b-2fd5843bbbc9
-- title:
--   QDL
-- statement:
--   Axiom (QDL), the quasi submodularity of a set $D$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.200, axiom (QDL).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.200, axiom (QDL)

import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (QDL), the quasi submodularity of a set `D`. -/
def QDL (D : Set (V → ℤ)) : Prop := ∀ p ∈ D, ∀ q ∈ D, p ⊓ q ∈ D ∨ p ⊔ q ∈ D

end DiscreteConvex.LConvexFunctionsD


