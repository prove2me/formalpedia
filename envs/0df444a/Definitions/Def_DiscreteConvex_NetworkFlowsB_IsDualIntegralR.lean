-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_IsDualIntegralR
-- name    : DiscreteConvex_NetworkFlowsB_IsDualIntegralR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:23:31.172277+00:00
-- url     : https://prove2.me/theorems/193827e3-4e22-43f3-bff0-d1cab6140710
-- title:
--   IsDualIntegralR
-- statement:
--   $f$ is dual integral: every point of its domain has an integer subgradient.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.261, notation M[R→R|Z].)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.261, notation M[R→R|Z]

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_SubDifferentialR

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- `f` is dual integral: every point of its domain has an integer subgradient. -/
def IsDualIntegralR (f : (V → ℝ) → WithTop ℝ) : Prop :=
  ∀ p : V → ℝ, f p ≠ ⊤ → ∃ y : V → ℤ, (fun v => (y v : ℝ)) ∈ SubDifferentialR f p

end DiscreteConvex.NetworkFlowsB


