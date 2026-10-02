-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_L2Convex
-- name    : DiscreteConvex_ConjugacyDualityC_L2Convex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:43:20.068328+00:00
-- url     : https://prove2.me/theorems/ccf7ac02-aa2b-47b1-be45-989ec687c9cd
-- title:
--   L2Convex
-- statement:
--   $g$ is L2-convex: the integer infimal convolution of two L-convex functions.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.229.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.229

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_SBF
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_TRF
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_InfConv
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_InfConvE

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g` is L2-convex: the integer infimal convolution of two L-convex functions, required (as the book does) to be `> -∞`:
`InfConv` takes its infimum in the conditionally complete `WithTop ℝ` and reads the junk value
`0` when the values are unbounded below. -/
def L2Convex (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∃ g1 g2 : (V → ℤ) → WithTop ℝ, (SBF g1 ∧ TRF g1) ∧ (SBF g2 ∧ TRF g2) ∧
    (∀ p, InfConvE g1 g2 p ≠ ⊥) ∧ g = InfConv g1 g2

end DiscreteConvex.ConjugacyDualityC


