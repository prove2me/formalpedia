-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_IsCycle
-- name    : DiscreteConvex_NetworkFlowsC_IsCycle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:49:50.758862+00:00
-- url     : https://prove2.me/theorems/aad2de89-0ac2-4203-8ec4-02e8b66ea89d
-- title:
--   IsCycle
-- statement:
--   A closed walk in a digraph.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.265, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.265, redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def IsCycle {Arc W : Type*} (tail head : Arc → W) (k : ℕ) (a : Fin (k+1) → Arc) : Prop :=
  ∀ i : Fin (k+1), head (a i) = tail (a (i+1))

end DiscreteConvex.NetworkFlowsC


