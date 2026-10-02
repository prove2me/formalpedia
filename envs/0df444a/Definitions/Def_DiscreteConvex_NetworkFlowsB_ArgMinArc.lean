-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_ArgMinArc
-- name    : DiscreteConvex_NetworkFlowsB_ArgMinArc
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:21:16.79888+00:00
-- url     : https://prove2.me/theorems/89cf50b3-0b4c-4319-82b6-ea52982b5b6c
-- title:
--   ArgMinArc
-- statement:
--   The minimizer set of a univariate real function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, standard notion, univariate.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, standard notion, univariate

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The minimizer set of a univariate real function. -/
def ArgMinArc (g : ℝ → WithTop ℝ) : Set ℝ := {t | ∀ s, g t ≤ g s}

end DiscreteConvex.NetworkFlowsB


