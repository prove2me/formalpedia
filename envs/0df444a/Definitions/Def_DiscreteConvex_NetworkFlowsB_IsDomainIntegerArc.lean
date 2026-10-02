-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_IsDomainIntegerArc
-- name    : DiscreteConvex_NetworkFlowsB_IsDomainIntegerArc
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:21:04.093922+00:00
-- url     : https://prove2.me/theorems/000ce555-e687-434d-b6fe-09b7f615c372
-- title:
--   IsDomainIntegerArc
-- statement:
--   $g:\mathbb R\to\mathbb R\cup\{+\infty\}$ has integer effective domain (a "primal integral" arc cost).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.261, notation C[Z|R→R].)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.261, notation C[Z|R→R]

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- `g : R → R ∪ {+∞}` has integer effective domain (a "primal integral" arc cost). -/
def IsDomainIntegerArc (g : ℝ → WithTop ℝ) : Prop := ∀ t : ℝ, g t ≠ ⊤ → ∃ k : ℤ, t = (k : ℝ)

end DiscreteConvex.NetworkFlowsB


