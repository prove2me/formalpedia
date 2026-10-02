-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_QEXC
-- name    : DiscreteConvex_MConvexFunctionsE_QEXC
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:05:34.794512+00:00
-- url     : https://prove2.me/theorems/54cf3919-f68e-446e-abc5-6da0bc51918b
-- title:
--   QEXC
-- statement:
--   Axiom (Q-EXC): the quasi M-convexity exchange axiom for a set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.171, axiom (Q-EXC).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.171, axiom (Q-EXC)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppNeg

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (Q-EXC): the quasi M-convexity exchange axiom for a set. -/
def QEXC (B : Set (V → ℤ)) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    (fun w => x w - CharVec u w + CharVec v w) ∈ B ∨
      (fun w => y w + CharVec u w - CharVec v w) ∈ B

end DiscreteConvex.MConvexFunctionsE


