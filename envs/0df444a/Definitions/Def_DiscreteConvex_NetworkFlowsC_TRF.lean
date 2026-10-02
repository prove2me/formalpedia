-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_TRF
-- name    : DiscreteConvex_NetworkFlowsC_TRF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:48:00.217163+00:00
-- url     : https://prove2.me/theorems/5f1477bd-ea5d-41a1-b93c-105fa3cfd957
-- title:
--   TRF
-- statement:
--   Axiom (TRF[Z]): $\exists r$, $g(p+\mathbf 1)=g(p)+r$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (TRF[Z]), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (TRF[Z]), redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Axiom (TRF[Z]). -/
def TRF (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∃ r : ℝ, ∀ p : V → ℤ, g (p + 1) = g p + (r : WithTop ℝ)

end DiscreteConvex.NetworkFlowsC


