-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsB_ConvexClosureVal
-- name    : DiscreteConvex_LConvexFunctionsB_ConvexClosureVal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:24:17.897021+00:00
-- url     : https://prove2.me/theorems/0f7083f2-2f03-47a0-b1f1-a50d99ababa0
-- title:
--   ConvexClosureVal
-- statement:
--   The convex closure $\bar g(x)$ of $g$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Eq. (3.57)-adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Eq. (3.57)-adjacent

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_DomZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_ConvexClosureValOn

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The convex closure `ḡ(x)` of `g`. -/
noncomputable def ConvexClosureVal (g : (V → ℤ) → WithTop ℝ) (x : V → ℝ) : WithTop ℝ :=
  sInf {L : WithTop ℝ | ∃ (S : Finset (V → ℤ)),
    (∀ y ∈ S, y ∈ DomZ g) ∧ L = ConvexClosureValOn g S x}

end DiscreteConvex.LConvexFunctionsB


