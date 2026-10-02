-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_MExchangeAxiom
-- name    : DiscreteConvex_ConjugacyDualityD_MExchangeAxiom
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:57:51.626298+00:00
-- url     : https://prove2.me/theorems/dcde0862-cc39-4ac0-8511-f1d816315b04
-- title:
--   MExchangeAxiom
-- statement:
--   Axiom (M-EXC[Z]): $f$ is an M-convex function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, Eq. (6.1), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, Eq. (6.1), redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IndicatorVec
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_SuppPos
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_SuppNeg

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (M-EXC[Z]): `f` is an M-convex function. -/
def MExchangeAxiom (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    f x + f y ≥ f (fun w => x w - IndicatorVec {u} w + IndicatorVec {v} w) +
      f (fun w => y w + IndicatorVec {u} w - IndicatorVec {v} w)

end DiscreteConvex.ConjugacyDualityD


