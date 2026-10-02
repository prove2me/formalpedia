-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_L2Convex
-- name    : DiscreteConvex_ConjugacyDualityD_L2Convex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:58:02.986095+00:00
-- url     : https://prove2.me/theorems/6ac536ba-ffdb-41d6-b11c-da88a75d3202
-- title:
--   L2Convex
-- statement:
--   $g$ is L2-convex: the integer infimal convolution of two L-convex functions.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.229, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.229, redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_SBF
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_TRF
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_InfConv

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g` is L2-convex: the integer infimal convolution of two L-convex functions. -/
def L2Convex (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∃ g1 g2 : (V → ℤ) → WithTop ℝ, (SBF g1 ∧ TRF g1) ∧ (SBF g2 ∧ TRF g2) ∧ g = InfConv g1 g2

end DiscreteConvex.ConjugacyDualityD


