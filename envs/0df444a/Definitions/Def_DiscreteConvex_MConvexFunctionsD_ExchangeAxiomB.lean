-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_ExchangeAxiomB
-- name    : DiscreteConvex_MConvexFunctionsD_ExchangeAxiomB
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:50:22.329688+00:00
-- url     : https://prove2.me/theorems/83eb8c9f-5b5c-4f68-971b-ebb7915dad27
-- title:
--   ExchangeAxiomB
-- statement:
--   Axiom (B-EXC[Z]): $B$ is an M-convex set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_SuppNeg

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def ExchangeAxiomB (B : Set (V → ℤ)) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    (fun w => x w - CharVec u w + CharVec v w) ∈ B ∧
    (fun w => y w + CharVec u w - CharVec v w) ∈ B

end DiscreteConvex.MConvexFunctionsD


