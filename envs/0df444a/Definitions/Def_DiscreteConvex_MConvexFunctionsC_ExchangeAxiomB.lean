-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_ExchangeAxiomB
-- name    : DiscreteConvex_MConvexFunctionsC_ExchangeAxiomB
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:24:11.606282+00:00
-- url     : https://prove2.me/theorems/277a84a7-683c-4db1-bf7e-dbca928a3034
-- title:
--   ExchangeAxiomB
-- statement:
--   Axiom (B-EXC[Z]): $B \subseteq \mathbb Z^V$ is an M-convex set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, axiom (B-EXC[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, axiom (B-EXC[Z])

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_SuppNeg

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def ExchangeAxiomB (B : Set (V → ℤ)) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    (fun w => x w - CharVec u w + CharVec v w) ∈ B ∧
    (fun w => y w + CharVec u w - CharVec v w) ∈ B

end DiscreteConvex.MConvexFunctionsC


