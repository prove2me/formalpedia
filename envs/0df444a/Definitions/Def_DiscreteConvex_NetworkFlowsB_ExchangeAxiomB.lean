-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_ExchangeAxiomB
-- name    : DiscreteConvex_NetworkFlowsB_ExchangeAxiomB
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:22:59.235697+00:00
-- url     : https://prove2.me/theorems/c7ae419b-919b-43ef-aed8-eafc06ac3a8f
-- title:
--   ExchangeAxiomB
-- statement:
--   Axiom (B-EXC[Z]): $B$ is an M-convex set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, axiom (B-EXC[Z]), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, axiom (B-EXC[Z]), redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_SuppPos
import Definitions.Def_DiscreteConvex_NetworkFlowsB_SuppNeg

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Axiom (B-EXC[Z]): `B` is an M-convex set. -/
def ExchangeAxiomB (B : Set (V → ℤ)) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    (fun w => x w - (if w = u then (1:ℤ) else 0) + (if w = v then (1:ℤ) else 0)) ∈ B ∧
    (fun w => y w + (if w = u then (1:ℤ) else 0) - (if w = v then (1:ℤ) else 0)) ∈ B

end DiscreteConvex.NetworkFlowsB


