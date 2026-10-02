-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_MNat2Convex
-- name    : DiscreteConvex_ConjugacyDualityD_MNat2Convex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:00:33.216294+00:00
-- url     : https://prove2.me/theorems/b969df58-e988-426f-a410-316fc93416a4
-- title:
--   MNat2Convex
-- statement:
--   $f$ is M$^\natural_2$-convex: the sum of two M$^\natural$-convex functions.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.226, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.226, redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MNaturalConvex

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f` is M♮₂-convex: the sum of two M♮-convex functions. -/
def MNat2Convex (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∃ f1 f2 : (V → ℤ) → WithTop ℝ, MNaturalConvex f1 ∧ MNaturalConvex f2 ∧
    f = fun x => f1 x + f2 x

end DiscreteConvex.ConjugacyDualityD


