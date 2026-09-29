-- Prove2me | Definitions.Def_OnlineConvexOpt_Blackwell_Approachability
-- name    : OnlineConvexOpt_Blackwell_Approachability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:51:56.513376+00:00
-- url     : https://prove2.me/theorems/bcd06342-9ada-454a-9f9e-1767ba974e5e
-- title:
--   Approachability (Definition 13.3)
-- statement:
--   Given a generalized vector game $K_1,K_2,u$ (Definition 13.2: $u:E_1\to E_2\to F$ the
--   vector payoff, $K_1\subseteq E_1$, $K_2\subseteq E_2$ the two players' decision sets), a
--   set $S\subseteq F$ is **approachable** (p. 209) if there is a non-anticipating algorithm
--   playing in $K_1$ such that, for every sequence $y_1,y_2,\dots\in K_2$, the running average
--   reward vector's distance to $S$ tends to $0$ as the horizon grows.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 209, Definition 13.3 (PDF p. 231)

import Mathlib

namespace OnlineConvexOpt.Blackwell

variable {E1 E2 F : Type*} [NormedAddCommGroup E1] [NormedAddCommGroup E2] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Definition 13.3 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 209, PDF p. 231). Given a generalized vector game `K1, K2, u` (Definition
13.2: `u : E1 → E2 → F` the vector payoff, `K1 ⊆ E1`, `K2 ⊆ E2` the two players' bounded convex
closed decision sets), a set `S ⊆ F` is **approachable** if there is a non-anticipating
algorithm `Astrat` playing in `K1` (`x_t ← Astrat(y_1,...,y_{t-1})`) such that for every sequence
`y_1, y_2, ... ∈ K2`, `Dist((1/T)∑_{t=1}^T u(x_t,y_t), S) → 0` as `T → ∞`. -/
def IsApproachable (K1 : Set E1) (K2 : Set E2) (u : E1 → E2 → F) (S : Set F) : Prop :=
  ∃ Astrat : (ℕ → E2) → ℕ → E1,
    (∀ y : ℕ → E2, ∀ t : ℕ, 1 ≤ t → Astrat y t ∈ K1) ∧
    (∀ y y' : ℕ → E2, ∀ t : ℕ, (∀ s, s < t → y s = y' s) → Astrat y t = Astrat y' t) ∧
    ∀ y : ℕ → E2, (∀ t : ℕ, 1 ≤ t → y t ∈ K2) →
      Filter.Tendsto
        (fun T : ℕ =>
          Metric.infDist ((T : ℝ)⁻¹ • ∑ t ∈ Finset.Icc 1 T, u (Astrat y t) (y t)) S)
        Filter.atTop (nhds 0)

end OnlineConvexOpt.Blackwell


