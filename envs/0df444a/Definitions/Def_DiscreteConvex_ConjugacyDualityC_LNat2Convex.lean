-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_LNat2Convex
-- name    : DiscreteConvex_ConjugacyDualityC_LNat2Convex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:43:33.63731+00:00
-- url     : https://prove2.me/theorems/0d00f5a3-9fa8-417f-ab94-fe2db11e6e8d
-- title:
--   LNat2Convex
-- statement:
--   $g$ is L$^\natural_2$-convex: the integer infimal convolution of two L$^\natural$-convex functions.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.229.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.229

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_LNaturalConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_InfConv
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_InfConvE

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g` is L♮₂-convex: the integer infimal convolution of two L♮-convex functions, required (as the book does) to be `> -∞`:
`InfConv` takes its infimum in the conditionally complete `WithTop ℝ` and reads the junk value
`0` when the values are unbounded below. -/
def LNat2Convex (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∃ g1 g2 : (V → ℤ) → WithTop ℝ, LNaturalConvex g1 ∧ LNaturalConvex g2 ∧
    (∀ p, InfConvE g1 g2 p ≠ ⊥) ∧ g = InfConv g1 g2

end DiscreteConvex.ConjugacyDualityC


