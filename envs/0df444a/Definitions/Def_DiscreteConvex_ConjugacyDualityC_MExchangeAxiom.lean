-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_MExchangeAxiom
-- name    : DiscreteConvex_ConjugacyDualityC_MExchangeAxiom
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:42:10.707119+00:00
-- url     : https://prove2.me/theorems/a19ab0a2-adce-4c14-a76d-744020ecb9ca
-- title:
--   MExchangeAxiom
-- statement:
--   Axiom (M-EXC[Z]): $f$ is an M-convex function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, Eq. (6.1).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, Eq. (6.1)

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_IndicatorVec
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_SuppPos
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_SuppNeg

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (M-EXC[Z]): `f` is an M-convex function. -/
def MExchangeAxiom (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    f x + f y ≥ f (fun w => x w - IndicatorVec {u} w + IndicatorVec {v} w) +
      f (fun w => y w + IndicatorVec {u} w - IndicatorVec {v} w)

end DiscreteConvex.ConjugacyDualityC


