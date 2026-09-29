-- Prove2me | Definitions.Def_OnlinePrimalDual_Caching_DualObjective
-- name    : OnlinePrimalDual_Caching_DualObjective
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:46:34.677718+00:00
-- url     : https://prove2.me/theorems/6256ffac-dd16-424f-a660-54d71a7db9f3
-- title:
--   The caching LP's dual objective
-- statement:
--   `DualObjective inst y z := ∑_t rhs(t)·y(t) − ∑_v z(v)`, the dual program's own objective
--   (p. 152): maximize `∑ₜ rhs(t)y(t) − ∑ᵥ z(v)` subject to `∀v, dualSum y v − z v ≤ c(v)`,
--   `y,z ≥ 0`. Added per `CHANGES_REQUESTED.md`'s required fix to `algorithm_competitive_ratio`
--   (2026-09-21): unlike `04-framework`'s fixed `b(j)=1`, this chapter's `rhs` can be
--   non-positive, so a direct cost-to-cost comparison against an arbitrary offline solution is
--   unsound here, and the proof must route through this actual dual objective instead.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 152, Section 7.1.1

import Mathlib
import Definitions.Def_OnlinePrimalDual_Caching_CachingInstance

namespace OnlinePrimalDual.Caching

/-- The dual objective of this chapter's LP (p. 152, PDF p. 63): the caching LP's dual program
maximizes `∑ₜ rhs(t)·y(t) − ∑ᵥ z(v)` subject to `∀v, dualSum y v − z v ≤ c v`, `y,z ≥ 0` — the `z`
term is the dual variable of the primal's own `x(p,j) ≤ 1` box constraint. Named as its own
quantity (new item, added per `CHANGES_REQUESTED.md`'s required fix to `algorithm_competitive_ratio`)
because, unlike `04-framework`'s `CoveringInstance` (whose right-hand side is fixed at `b(j)=1`),
this chapter's `rhs` can be non-positive, so the direct "weak duality against an arbitrary feasible
offline comparison solution" shortcut used there is unsound here without routing explicitly through
this objective (see `Thm_OnlinePrimalDual_Caching_weak_duality`). -/
def DualObjective {V Time : Type*} [Fintype V] [Fintype Time] [DecidableEq V]
    (inst : CachingInstance V Time) (y : Time → ℝ) (z : V → ℝ) : ℝ :=
  ∑ t, inst.rhs t * y t - ∑ v, z v

end OnlinePrimalDual.Caching


