-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_MExchangeAxiom
-- name    : DiscreteConvex_NetworkFlowsC_MExchangeAxiom
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:53:04.784563+00:00
-- url     : https://prove2.me/theorems/b62e8f9e-051d-43de-a19d-a8408f0a8291
-- title:
--   MExchangeAxiom
-- statement:
--   Axiom (M-EXC[Z]): $f$ is an integer-domain M-convex function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, Eq. (6.1), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, Eq. (6.1), redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_DomZ
import Definitions.Def_DiscreteConvex_NetworkFlowsC_SuppPos
import Definitions.Def_DiscreteConvex_NetworkFlowsC_SuppNeg

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Axiom (M-EXC[Z]). -/
def MExchangeAxiom (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    f x + f y ≥
      f (fun w => x w - (if w = u then (1:ℤ) else 0) + (if w = v then (1:ℤ) else 0)) +
      f (fun w => y w + (if w = u then (1:ℤ) else 0) - (if w = v then (1:ℤ) else 0))

end DiscreteConvex.NetworkFlowsC


