-- Prove2me | Definitions.Def_TeschlODE_Horseshoe_IsHorseshoeMap
-- name    : TeschlODE_Horseshoe_IsHorseshoeMap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T05:48:44.57017+00:00
-- url     : https://prove2.me/theorems/7e4a0a08-b66b-4489-a4bd-6bb09b9e8ce6
-- title:
--   The Smale horseshoe map on the strips $J_0, J_1$ (13.1)–(13.3)
-- statement:
--   Fix $\lambda, \mu$ and set $J_0 = [0,1] \times [0, 1/\mu]$ and $J_1 = [0,1] \times [1 - 1/\mu, 1]$ (13.1). A map $F : \mathbb{R}^2 \to \mathbb{R}^2$ is a **Smale horseshoe map** if
--   $$F(x, y) = (\lambda x, \mu y) \text{ on } J_0, \qquad F(x, y) = (1 - \lambda x, \mu (1 - y)) \text{ on } J_1.$$
--   The book describes the map analytically only on $J_0 \cup J_1$: "since we are only interested in the dynamics on $D$, we only describe this part of the map analytically" (p. 331). The rest of the picture, the fold that turns the stretched square into a horseshoe, is not part of the statement.
--
--   **Formalization Note.** A predicate on $F$: the values of $F$ off $J_0 \cup J_1$ are arbitrary, so every theorem quantifies over all such extensions. For $\mu > 2$ the strips are disjoint and such maps exist. For $\mu = 2$ they meet on $y = 1/2$, where the two formulas disagree.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 332, §13.1, Eqs. (13.1)–(13.3)

import Mathlib

namespace TeschlODE.Horseshoe

/-- Teschl, §13.1, p. 332, (13.1)–(13.3): `F : ℝ² → ℝ²` is a Smale horseshoe map with parameters
`λ`, `µ` if on the strips `J₀ = [0, 1] × [0, 1/µ]` and `J₁ = [0, 1] × [1 − 1/µ, 1]` it is given by
`F(x, y) = (λx, µy)` on `J₀` (13.2) and `F(x, y) = (1 − λx, µ(1 − y))` on `J₁` (13.3). The book
describes the map analytically only on `J₀ ∪ J₁` ("we only describe this part of the map
analytically", p. 331), so its values elsewhere are left arbitrary. For `µ > 2` the strips are
disjoint, so such maps exist. -/
def IsHorseshoeMap (lam μ : ℝ) (F : ℝ × ℝ → ℝ × ℝ) : Prop :=
  (∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (1 / μ), F p = (lam * p.1, μ * p.2)) ∧
    (∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (1 - 1 / μ) 1, F p = (1 - lam * p.1, μ * (1 - p.2)))

end TeschlODE.Horseshoe


