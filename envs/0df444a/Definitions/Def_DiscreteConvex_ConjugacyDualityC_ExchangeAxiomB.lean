-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_ExchangeAxiomB
-- name    : DiscreteConvex_ConjugacyDualityC_ExchangeAxiomB
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:42:23.660933+00:00
-- url     : https://prove2.me/theorems/aa91b566-9e98-4f95-a35a-0aab9fa264ab
-- title:
--   ExchangeAxiomB
-- statement:
--   Axiom (B-EXC[Z]): $B$ is an M-convex set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, axiom (B-EXC[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, axiom (B-EXC[Z])

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_IndicatorVec
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_SuppPos
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_SuppNeg

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (B-EXC[Z]): `B` is an M-convex set. -/
def ExchangeAxiomB (B : Set (V → ℤ)) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    (fun w => x w - IndicatorVec {u} w + IndicatorVec {v} w) ∈ B ∧
    (fun w => y w + IndicatorVec {u} w - IndicatorVec {v} w) ∈ B

end DiscreteConvex.ConjugacyDualityC


