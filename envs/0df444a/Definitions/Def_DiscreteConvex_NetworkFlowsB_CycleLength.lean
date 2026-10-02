-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_CycleLength
-- name    : DiscreteConvex_NetworkFlowsB_CycleLength
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:21:30.983339+00:00
-- url     : https://prove2.me/theorems/cca105e0-ea97-4fc3-9d77-f908185614e8
-- title:
--   CycleLength
-- statement:
--   The length of a closed walk.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.251-252, adjacent to the negative-cycle definition.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.251-252, adjacent to the negative-cycle definition

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The length of a closed walk. -/
def CycleLength {Arc : Type*} (l : Arc → WithTop ℝ) (k : ℕ) (a : Fin (k+1) → Arc) : WithTop ℝ :=
  ∑ i : Fin (k+1), l (a i)

end DiscreteConvex.NetworkFlowsB


