-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_ArgMinArcZ
-- name    : DiscreteConvex_NetworkFlowsB_ArgMinArcZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:21:40.773638+00:00
-- url     : https://prove2.me/theorems/3fa90508-b111-44b0-8e61-d17ced9cadbe
-- title:
--   ArgMinArcZ
-- statement:
--   The minimizer set of a univariate integer function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, standard notion, univariate integer.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, standard notion, univariate integer

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The minimizer set of a univariate integer function. -/
def ArgMinArcZ (g : ℤ → WithTop ℝ) : Set ℤ := {t | ∀ s, g t ≤ g s}

end DiscreteConvex.NetworkFlowsB


