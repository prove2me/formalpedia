-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNat2Convex
-- name    : DiscreteConvex_ConjugacyDualityB_MNat2Convex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:34:28.733113+00:00
-- url     : https://prove2.me/theorems/0bb42310-c6a4-4e02-8e5b-d204fcc2c840
-- title:
--   MNat2Convex
-- statement:
--   $f$ is M$^\natural_2$-convex: the sum of two M$^\natural$-convex functions.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.226.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.226

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNaturalConvex

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f` is M♮₂-convex: the sum of two M♮-convex functions. -/
def MNat2Convex (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∃ f1 f2 : (V → ℤ) → WithTop ℝ, MNaturalConvex f1 ∧ MNaturalConvex f2 ∧
    f = fun x => f1 x + f2 x

end DiscreteConvex.ConjugacyDualityB


