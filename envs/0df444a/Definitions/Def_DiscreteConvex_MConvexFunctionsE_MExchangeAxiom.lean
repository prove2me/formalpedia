-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_MExchangeAxiom
-- name    : DiscreteConvex_MConvexFunctionsE_MExchangeAxiom
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:05:12.459276+00:00
-- url     : https://prove2.me/theorems/1ef2a2ad-9665-4361-b3e0-4340530902f4
-- title:
--   MExchangeAxiom
-- statement:
--   Axiom (M-EXC[Z]): $f$ is an M-convex function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, Eq. (6.1).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, Eq. (6.1)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomZ

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (M-EXC[Z]): `f` is an M-convex function. -/
def MExchangeAxiom (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    f x + f y ≥ f (fun w => x w - CharVec u w + CharVec v w) +
      f (fun w => y w + CharVec u w - CharVec v w)

end DiscreteConvex.MConvexFunctionsE


