-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_MExchangeAxiom
-- name    : DiscreteConvex_MConvexFunctionsD_MExchangeAxiom
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:51:14.842195+00:00
-- url     : https://prove2.me/theorems/49eabcb0-f4df-4ddd-b72e-87615190d995
-- title:
--   MExchangeAxiom
-- statement:
--   Axiom (M-EXC[Z]): $f$ is an M-convex function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, Eq. (6.1).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, Eq. (6.1)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_DomZ

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def MExchangeAxiom (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    f x + f y ≥ f (fun w => x w - CharVec u w + CharVec v w) +
      f (fun w => y w + CharVec u w - CharVec v w)

end DiscreteConvex.MConvexFunctionsD


