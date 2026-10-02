-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_ExchangeAxiomB
-- name    : DiscreteConvex_LConvexFunctionsD_ExchangeAxiomB
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:02:28.122518+00:00
-- url     : https://prove2.me/theorems/fef7fe6d-d2f3-4d20-ab75-5abd9f610202
-- title:
--   ExchangeAxiomB
-- statement:
--   Axiom (B-EXC[Z]): $B$ is an M-convex set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, axiom (B-EXC[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, axiom (B-EXC[Z])

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_IndicatorVec
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SuppPos
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SuppNeg

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (B-EXC[Z]): `B` is an M-convex set. -/
def ExchangeAxiomB (B : Set (V → ℤ)) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    (fun w => x w - IndicatorVec {u} w + IndicatorVec {v} w) ∈ B ∧
    (fun w => y w + IndicatorVec {u} w - IndicatorVec {v} w) ∈ B

end DiscreteConvex.LConvexFunctionsD


