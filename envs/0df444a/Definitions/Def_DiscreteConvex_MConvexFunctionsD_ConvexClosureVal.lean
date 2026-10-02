-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_ConvexClosureVal
-- name    : DiscreteConvex_MConvexFunctionsD_ConvexClosureVal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:52:18.041032+00:00
-- url     : https://prove2.me/theorems/336d4c90-f89a-4590-9082-ddc23ef532ec
-- title:
--   ConvexClosureVal
-- statement:
--   The convex closure $\bar f(x)$ of $f$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Eq. (3.57)-adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Eq. (3.57)-adjacent

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_ConvexClosureValOn

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The convex closure `f̄ : Rⱽ → R ∪ {±∞}` of `f`. -/
noncomputable def ConvexClosureVal (f : (V → ℤ) → WithTop ℝ) (x : V → ℝ) : WithTop ℝ :=
  sInf {L : WithTop ℝ | ∃ (S : Finset (V → ℤ)),
    (∀ y ∈ S, y ∈ DomZ f) ∧ L = ConvexClosureValOn f S x}

end DiscreteConvex.MConvexFunctionsD


