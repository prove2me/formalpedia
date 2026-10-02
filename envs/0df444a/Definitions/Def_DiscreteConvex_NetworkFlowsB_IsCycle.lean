-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_IsCycle
-- name    : DiscreteConvex_NetworkFlowsB_IsCycle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:21:29.176966+00:00
-- url     : https://prove2.me/theorems/127fa8fc-9d32-4269-8c67-189286bf7824
-- title:
--   IsCycle
-- statement:
--   A closed walk $a:\mathrm{Fin}(k+1)\to\mathrm{Arc}$ in a digraph.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.251-252, adjacent to the negative-cycle definition.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.251-252, adjacent to the negative-cycle definition

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- A closed walk `a : Fin (k+1) → Arc` in a digraph `(tail,head)`. -/
def IsCycle {Arc W : Type*} (tail head : Arc → W) (k : ℕ) (a : Fin (k+1) → Arc) : Prop :=
  ∀ i : Fin (k+1), head (a i) = tail (a (i+1))

end DiscreteConvex.NetworkFlowsB


