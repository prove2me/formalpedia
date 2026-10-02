-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_MExchangeAxiom
-- name    : DiscreteConvex_MConvexFunctionsC_MExchangeAxiom
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:24:14.916529+00:00
-- url     : https://prove2.me/theorems/dd4b4ab5-1c7d-4210-8a22-a936fdeb2701
-- title:
--   MExchangeAxiom
-- statement:
--   Axiom (M-EXC[Z]): $f$ is an **M-convex function**.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, Eq. (6.1).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, Eq. (6.1)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_DomZ

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def MExchangeAxiom (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    f x + f y ≥ f (fun w => x w - CharVec u w + CharVec v w) +
      f (fun w => y w + CharVec u w - CharVec v w)

end DiscreteConvex.MConvexFunctionsC


