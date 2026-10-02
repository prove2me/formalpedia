-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_OptP
-- name    : DiscreteConvex_ConjugacyDualityD_OptP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:58:36.13102+00:00
-- url     : https://prove2.me/theorems/3a2e1773-750f-4178-aec2-1bd94c41cd44
-- title:
--   OptP
-- statement:
--   The optimal-solution set of the primal problem at a given optimal value.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.240, Eq. (8.66)-adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.240, Eq. (8.66)-adjacent

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ToEReal

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The optimal-solution set of the primal problem at a given optimal value. -/
def OptP (c : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ)) (val : EReal) : Set (V → ℤ) :=
  {x ∈ B | ToEReal (c x) = val}

end DiscreteConvex.ConjugacyDualityD


