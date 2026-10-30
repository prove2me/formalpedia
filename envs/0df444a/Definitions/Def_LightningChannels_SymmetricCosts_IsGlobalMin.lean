-- Prove2me | Definitions.Def_LightningChannels_SymmetricCosts_IsGlobalMin
-- name    : LightningChannels_SymmetricCosts_IsGlobalMin
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:36:55.815611+00:00
-- url     : https://prove2.me/theorems/9d513d5e-63bc-4fca-8df2-7e16f7196e36
-- title:
--   Positive real balances and attained global channel optimality
-- statement:
--   Fix real reset cost $B$, common payment rate $\lambda$, and discount rate $r$. The positive quadrant is the set of real pairs $(x,y)$ with $x>0$ and $y>0$. Write $c^{x,y}(\lambda,\lambda)$ for the published exact analytic expression (3), using the roots (4). The predicate $\operatorname{IsGlobalMin}(B,\lambda,r,x,y)$ means
--
--   $$x>0,\quad y>0,\quad
--     c^{x,y}(\lambda,\lambda)\le c^{u,v}(\lambda,\lambda)
--     \quad\text{for every }u,v>0.$$
--
--   This interface records feasibility and attainment. Positivity of the economic parameters is supplied by the theorems using it. Neither equal balances nor first-order conditions nor an approximation belongs to this definition.
--
--   Differences from the source:
--   - reading: channel sizes in the unit-payment model → all positive real sizes in the exact analytic cost; reason: the source differentiates the closed-form objective on printed pp. 10–11 / PDF pp. 11–12 and explicitly uses a real solution on printed p. 12 / PDF p. 13; no fractional-barrier stochastic claim is made
--   - encoding: minimum over channel balances → positive feasibility and comparison with every positive real pair; reason: this expresses attained global optimality without defining symmetry, stationarity or asymptotic estimates into the predicate
-- source:
--   Guasoni, P.; Huberman, G.; Shikhelman, C., Lightning Network Economics: Channels, Management Science, Articles in Advance, published online November 6, 2023, https://doi.org/10.1287/mnsc.2022.01664, §3 and (3)–(4), printed pp. 5–6 / PDF pp. 6–7; Proof of Theorem 2(ii), printed p. 11 / PDF p. 12.

import Definitions.Def_LNChannels_RateBounds_ClosedForms

set_option autoImplicit false

namespace LightningChannels.SymmetricCosts

/-- The full continuous feasible domain; equal balances are not imposed. -/
def positiveQuadrant : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ 0 < p.2}

/-- Positive feasibility and comparison against every positive real balance pair.
The cost is the published exact expression (3), not an asymptotic approximation. -/
def IsGlobalMin (B rate r x y : ℝ) : Prop :=
  (x, y) ∈ positiveQuadrant ∧
    ∀ u v : ℝ, (u, v) ∈ positiveQuadrant →
      LNChannels.RateBounds.biCost rate rate r B x y ≤
        LNChannels.RateBounds.biCost rate rate r B u v

end LightningChannels.SymmetricCosts


