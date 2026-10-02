-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_MExchangeAxiom
-- name    : DiscreteConvex_ConjugacyDualityB_MExchangeAxiom
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:30:23.183338+00:00
-- url     : https://prove2.me/theorems/88f54ca3-1060-4718-bc25-f75081f2d980
-- title:
--   MExchangeAxiom
-- statement:
--   Axiom (M-EXC[Z]): $f$ is an M-convex function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, Eq. (6.1).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, Eq. (6.1)

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IndicatorVec
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_SuppPos
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_SuppNeg

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (M-EXC[Z]): `f` is an M-convex function. -/
def MExchangeAxiom (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    f x + f y ≥ f (fun w => x w - IndicatorVec {u} w + IndicatorVec {v} w) +
      f (fun w => y w + IndicatorVec {u} w - IndicatorVec {v} w)

end DiscreteConvex.ConjugacyDualityB


