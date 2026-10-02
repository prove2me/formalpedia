-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_ConvexClosureVal
-- name    : DiscreteConvex_ConjugacyDualityC_ConvexClosureVal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:43:58.665243+00:00
-- url     : https://prove2.me/theorems/66267388-fb3b-472f-8e71-ac287086c3db
-- title:
--   ConvexClosureVal
-- statement:
--   The convex closure $\bar f(x)$ of $f$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Eq. (3.57)-adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Eq. (3.57)-adjacent

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_ConvexClosureValOn

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The convex closure `f̄(x)` of `f`. -/
noncomputable def ConvexClosureVal (f : (V → ℤ) → WithTop ℝ) (x : V → ℝ) : WithTop ℝ :=
  sInf {L : WithTop ℝ | ∃ (S : Finset (V → ℤ)),
    (∀ y ∈ S, y ∈ DomZ f) ∧ L = ConvexClosureValOn f S x}

end DiscreteConvex.ConjugacyDualityC


