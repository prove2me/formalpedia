-- Prove2me | Definitions.Def_FreePlayPremium_OptimalPolicies_AdvertisingCost
-- name    : FreePlayPremium_OptimalPolicies_AdvertisingCost
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T23:27:14.806316+00:00
-- url     : https://prove2.me/theorems/39f8eda3-9253-4d56-830d-08c2d01def38
-- title:
--   Increasing strictly convex twice differentiable advertising cost
-- statement:
--   An advertising cost is a real function $C$ on nonnegative advertising strengths with first and second derivative functions $C_1,C_2$ such that, at every $a\ge0$, $C$ has derivative $C_1(a)$ within $[0,\infty)$, $C_1$ has derivative $C_2(a)$ within that half-line, and $C_1(a)>0$, $C_2(a)>0$. Derivatives at zero are right derivatives. The class does not fix $C(0)$, demand continuous second derivatives, impose coercivity, or specialize to quadratic costs. Values of the real function outside its nonnegative domain are irrelevant.
-- source:
--   Mai and Hu (2022), Optimizing Free-to-Play Multiplayer Games with Premium Subscription, Management Science, https://doi.org/10.1287/mnsc.2022.4510, §5, printed p. 13 (PDF p. 13)

import Mathlib

open Set

namespace FreePlayPremium.OptimalPolicies

/-- Twice differentiable cost on the nonnegative half-line; at zero derivatives
are right derivatives. No normalization or growth assumption is imposed. -/
def AdvertisingCost (C : ℝ → ℝ) : Prop :=
  ∃ d₁ d₂ : ℝ → ℝ, ∀ a ∈ Ici (0 : ℝ),
    HasDerivWithinAt C (d₁ a) (Ici 0) a ∧
    HasDerivWithinAt d₁ (d₂ a) (Ici 0) a ∧
    0 < d₁ a ∧ 0 < d₂ a

end FreePlayPremium.OptimalPolicies


