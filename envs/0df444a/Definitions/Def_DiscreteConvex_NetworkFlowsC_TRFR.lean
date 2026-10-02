-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_TRFR
-- name    : DiscreteConvex_NetworkFlowsC_TRFR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:48:59.680977+00:00
-- url     : https://prove2.me/theorems/582dd3ab-6db0-49d4-8144-fefa321e83c3
-- title:
--   TRFR
-- statement:
--   Axiom (TRF[R]): $\exists r$, $g(p+\mathbf 1)=g(p)+r$, real domain.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, redeclared, real version.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, redeclared, real version

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def TRFR (g : (V → ℝ) → WithTop ℝ) : Prop :=
  ∃ r : ℝ, ∀ p : V → ℝ, g (fun v => p v + 1) = g p + (r : WithTop ℝ)

end DiscreteConvex.NetworkFlowsC


