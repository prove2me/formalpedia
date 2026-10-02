-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_CycleLength
-- name    : DiscreteConvex_NetworkFlowsC_CycleLength
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:49:51.523394+00:00
-- url     : https://prove2.me/theorems/3a53b2c3-d6dd-4775-8d21-e0e542598832
-- title:
--   CycleLength
-- statement:
--   The length of a closed walk.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.265, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.265, redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def CycleLength {Arc : Type*} (l : Arc → WithTop ℝ) (k : ℕ) (a : Fin (k+1) → Arc) : WithTop ℝ :=
  ∑ i : Fin (k+1), l (a i)

end DiscreteConvex.NetworkFlowsC


