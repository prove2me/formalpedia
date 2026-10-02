-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_MExchangeAxiomR
-- name    : DiscreteConvex_NetworkFlowsC_MExchangeAxiomR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:53:11.041592+00:00
-- url     : https://prove2.me/theorems/6c94498f-1d15-4dd7-a5af-95d19459ee9a
-- title:
--   MExchangeAxiomR
-- statement:
--   Axiom (M-EXC[R]): $f$ is a real-domain M-convex function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133-134, axiom (M-EXC[R]), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133-134, axiom (M-EXC[R]), redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_DomR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_SuppPosR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_SuppNegR

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Axiom (M-EXC[R]). -/
def MExchangeAxiomR (g : (V → ℝ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomR g, ∀ y ∈ DomR g, ∀ u ∈ SuppPosR x y, ∃ v ∈ SuppNegR x y, ∃ alpha0 : ℝ, 0 < alpha0 ∧
    ∀ alpha : ℝ, 0 ≤ alpha → alpha ≤ alpha0 →
      g x + g y ≥
        g (fun w => x w - alpha * (if w = u then (1:ℝ) else 0) + alpha * (if w = v then (1:ℝ) else 0)) +
        g (fun w => y w + alpha * (if w = u then (1:ℝ) else 0) - alpha * (if w = v then (1:ℝ) else 0))

end DiscreteConvex.NetworkFlowsC


