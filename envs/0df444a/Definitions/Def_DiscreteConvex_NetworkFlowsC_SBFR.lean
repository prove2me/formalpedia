-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_SBFR
-- name    : DiscreteConvex_NetworkFlowsC_SBFR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:48:59.211378+00:00
-- url     : https://prove2.me/theorems/7b23bb22-4422-452d-a10d-9e20e85bb05c
-- title:
--   SBFR
-- statement:
--   Axiom (SBF[R]): $g(p)+g(q)\ge g(p\vee q)+g(p\wedge q)$, real domain.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, redeclared, real version.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, redeclared, real version

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def SBFR (g : (V → ℝ) → WithTop ℝ) : Prop :=
  ∀ p q : V → ℝ, g p + g q ≥ g (fun v => max (p v) (q v)) + g (fun v => min (p v) (q v))

end DiscreteConvex.NetworkFlowsC


