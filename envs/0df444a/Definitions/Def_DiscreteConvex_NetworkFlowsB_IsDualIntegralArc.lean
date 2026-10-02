-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_IsDualIntegralArc
-- name    : DiscreteConvex_NetworkFlowsB_IsDualIntegralArc
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:23:24.712094+00:00
-- url     : https://prove2.me/theorems/427d4c2b-95e7-4a25-8a3f-346b58744b0a
-- title:
--   IsDualIntegralArc
-- statement:
--   $g$ is dual integral: every point of its domain has an integer subgradient.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.261, notation C[R→R|Z].)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.261, notation C[R→R|Z]

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_SubDifferentialArc

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- `g` is dual integral: every point of its domain has an integer subgradient. -/
def IsDualIntegralArc (g : ℝ → WithTop ℝ) : Prop :=
  ∀ t : ℝ, g t ≠ ⊤ → ∃ n : ℤ, (n : ℝ) ∈ SubDifferentialArc g t

end DiscreteConvex.NetworkFlowsB


