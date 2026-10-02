-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_ExchangeAxiomB
-- name    : DiscreteConvex_AlgorithmsB_ExchangeAxiomB
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:57:19.57927+00:00
-- url     : https://prove2.me/theorems/043d05f7-a528-49f3-bc9d-07671f974b36
-- title:
--   ExchangeAxiomB
-- statement:
--   Axiom (B-EXC[Z]): $B$ is an M-convex set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, axiom (B-EXC[Z]), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, axiom (B-EXC[Z]), redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_SuppPos
import Definitions.Def_DiscreteConvex_AlgorithmsB_SuppNeg

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (B-EXC[Z]): `B` is an M-convex set. -/
def ExchangeAxiomB (B : Set (V → ℤ)) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    (fun w => x w - (if w = u then (1:ℤ) else 0) + (if w = v then (1:ℤ) else 0)) ∈ B ∧
    (fun w => y w + (if w = u then (1:ℤ) else 0) - (if w = v then (1:ℤ) else 0)) ∈ B

end DiscreteConvex.AlgorithmsB


