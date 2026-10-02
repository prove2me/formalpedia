-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityB_RelInt
-- name    : DiscreteConvex_IntegralConvexityB_RelInt
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:59:23.635143+00:00
-- url     : https://prove2.me/theorems/c2cadac4-7d38-4985-ae94-4480985816ae
-- title:
--   Relative interior of a set
-- statement:
--   Points $x\in S$ with a metric ball around $x$, intersected with $\operatorname{aff}S$, contained in $S$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.98-99.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.98-99

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, pp.98-99: the relative interior of a set, in
`DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- The **relative interior** `ri S`: points `x ∈ S` such that `\{y : ‖y-x‖ < ε\} ∩ aff S ⊆ S`
for some `ε > 0` (p.99, verbatim). -/
def RelInt {V : Type*} [Fintype V] (S : Set (V → ℝ)) : Set (V → ℝ) :=
  {x | x ∈ S ∧ ∃ ε > 0, Metric.ball x ε ∩ (affineSpan ℝ S : Set (V → ℝ)) ⊆ S}

end DiscreteConvex.IntegralConvexityB


