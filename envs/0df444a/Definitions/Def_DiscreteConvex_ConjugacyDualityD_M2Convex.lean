-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_M2Convex
-- name    : DiscreteConvex_ConjugacyDualityD_M2Convex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:59:21.604226+00:00
-- url     : https://prove2.me/theorems/7223cbb6-9d25-4c40-a6b8-62f177372fd9
-- title:
--   M2Convex
-- statement:
--   $f$ is M2-convex: the sum of two M-convex functions.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.226, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.226, redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MExchangeAxiom

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f` is M2-convex: the sum of two M-convex functions. -/
def M2Convex (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∃ f1 f2 : (V → ℤ) → WithTop ℝ, MExchangeAxiom f1 ∧ MExchangeAxiom f2 ∧
    f = fun x => f1 x + f2 x

end DiscreteConvex.ConjugacyDualityD


