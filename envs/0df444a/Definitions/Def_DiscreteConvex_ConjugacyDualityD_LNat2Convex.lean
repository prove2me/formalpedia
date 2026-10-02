-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_LNat2Convex
-- name    : DiscreteConvex_ConjugacyDualityD_LNat2Convex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:59:28.563714+00:00
-- url     : https://prove2.me/theorems/812379bc-1ed5-4444-9915-638f06ffda7d
-- title:
--   LNat2Convex
-- statement:
--   $g$ is L$^\natural_2$-convex: the integer infimal convolution of two L$^\natural$-convex functions.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.229, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.229, redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_LNaturalConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_InfConv

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g` is L♮₂-convex: the integer infimal convolution of two L♮-convex functions. -/
def LNat2Convex (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∃ g1 g2 : (V → ℤ) → WithTop ℝ, LNaturalConvex g1 ∧ LNaturalConvex g2 ∧ g = InfConv g1 g2

end DiscreteConvex.ConjugacyDualityD


