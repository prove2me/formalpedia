-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_ExchangeAxiomB
-- name    : DiscreteConvex_ConjugacyDualityD_ExchangeAxiomB
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:57:58.73251+00:00
-- url     : https://prove2.me/theorems/34c709d1-d535-4fab-b65b-9263133bca9d
-- title:
--   ExchangeAxiomB
-- statement:
--   Axiom (B-EXC[Z]): $B$ is an M-convex set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, axiom (B-EXC[Z]), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, axiom (B-EXC[Z]), redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IndicatorVec
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_SuppPos
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_SuppNeg

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (B-EXC[Z]): `B` is an M-convex set. -/
def ExchangeAxiomB (B : Set (V → ℤ)) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    (fun w => x w - IndicatorVec {u} w + IndicatorVec {v} w) ∈ B ∧
    (fun w => y w + IndicatorVec {u} w - IndicatorVec {v} w) ∈ B

end DiscreteConvex.ConjugacyDualityD


