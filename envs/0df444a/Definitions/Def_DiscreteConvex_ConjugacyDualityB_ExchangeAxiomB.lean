-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_ExchangeAxiomB
-- name    : DiscreteConvex_ConjugacyDualityB_ExchangeAxiomB
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:30:54.341651+00:00
-- url     : https://prove2.me/theorems/33c1d64a-b8d4-42a6-a342-2e3f0fdeefc0
-- title:
--   ExchangeAxiomB
-- statement:
--   Axiom (B-EXC[Z]): $B$ is an M-convex set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, axiom (B-EXC[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, axiom (B-EXC[Z])

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IndicatorVec
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_SuppPos
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_SuppNeg

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (B-EXC[Z]): `B` is an M-convex set. -/
def ExchangeAxiomB (B : Set (V → ℤ)) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    (fun w => x w - IndicatorVec {u} w + IndicatorVec {v} w) ∈ B ∧
    (fun w => y w + IndicatorVec {u} w - IndicatorVec {v} w) ∈ B

end DiscreteConvex.ConjugacyDualityB


