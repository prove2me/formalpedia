-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_ConvexClosureVal
-- name    : DiscreteConvex_MConvexFunctionsC_ConvexClosureVal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:29:20.448925+00:00
-- url     : https://prove2.me/theorems/462af770-debe-4685-b343-08eafd975bf6
-- title:
--   ConvexClosureVal
-- statement:
--   The **convex closure** $\bar f(x)$ of $f$: the infimum, over finite convex combinations of points of $\operatorname{dom} f$ representing $x$, of the corresponding combination of function values.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Eq. (3.57)-adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Eq. (3.57)-adjacent

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ConvexClosureValOn

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The convex closure `f̄ : Rⱽ → R ∪ {±∞}` of `f`, Eq. (3.57)-adjacent: the infimum over convex
combinations of points of `dom f`. -/
noncomputable def ConvexClosureVal (f : (V → ℤ) → WithTop ℝ) (x : V → ℝ) : WithTop ℝ :=
  sInf {L : WithTop ℝ | ∃ (S : Finset (V → ℤ)),
    (∀ y ∈ S, y ∈ DomZ f) ∧ L = ConvexClosureValOn f S x}

end DiscreteConvex.MConvexFunctionsC


