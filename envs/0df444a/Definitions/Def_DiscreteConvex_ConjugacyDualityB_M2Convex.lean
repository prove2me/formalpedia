-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_M2Convex
-- name    : DiscreteConvex_ConjugacyDualityB_M2Convex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:33:37.335539+00:00
-- url     : https://prove2.me/theorems/d41919af-cb1c-4317-9d5a-0a7dca23d247
-- title:
--   M2Convex
-- statement:
--   $f$ is M2-convex: the sum of two M-convex functions.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.226.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.226

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MExchangeAxiom

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f` is M2-convex: the sum of two M-convex functions. -/
def M2Convex (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∃ f1 f2 : (V → ℤ) → WithTop ℝ, MExchangeAxiom f1 ∧ MExchangeAxiom f2 ∧
    f = fun x => f1 x + f2 x

end DiscreteConvex.ConjugacyDualityB


