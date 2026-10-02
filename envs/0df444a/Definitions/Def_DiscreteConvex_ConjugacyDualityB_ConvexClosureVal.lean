-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConvexClosureVal
-- name    : DiscreteConvex_ConjugacyDualityB_ConvexClosureVal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:32:18.878044+00:00
-- url     : https://prove2.me/theorems/987aa114-a62e-43b0-b6ac-d6ea6bf065e9
-- title:
--   ConvexClosureVal
-- statement:
--   The convex closure $\bar f(x)$ of $f$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Eq. (3.57)-adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Eq. (3.57)-adjacent

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConvexClosureValOn

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The convex closure `f̄(x)` of `f`. -/
noncomputable def ConvexClosureVal (f : (V → ℤ) → WithTop ℝ) (x : V → ℝ) : WithTop ℝ :=
  sInf {L : WithTop ℝ | ∃ (S : Finset (V → ℤ)),
    (∀ y ∈ S, y ∈ DomZ f) ∧ L = ConvexClosureValOn f S x}

end DiscreteConvex.ConjugacyDualityB


