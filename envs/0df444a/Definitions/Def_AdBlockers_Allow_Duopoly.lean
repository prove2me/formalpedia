-- Prove2me | Definitions.Def_AdBlockers_Allow_Duopoly
-- name    : AdBlockers_Allow_Duopoly
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:01.798771+00:00
-- url     : https://prove2.me/theorems/97099736-8ed3-429a-83e5-6506152c6a6f
-- title:
--   Hotelling duopoly with full coverage: clipped market share, and pure Nash equilibrium of a two-player game on [0, ∞)
-- statement:
--   Two general objects used by the ad-blocker model of Despotakis, Ravi and Srinivasan.
--
--   **Hotelling share with full coverage.** Two firms sit at the endpoints $0$ and $1$ of the unit interval, and a unit mass of consumers is spread uniformly over $[0,1]$. A consumer at position $x$ gets utility $m + (1-x) - d_1$ from firm 1 and $m + x - d_2$ from firm 2, where $d_1, d_2$ are the disutilities (ads or prices) the two firms impose, and buys from the firm that gives the higher utility; the intrinsic value $m$ is large enough that every consumer buys. The consumers who strictly prefer firm 1 are those with $x < (1 + d_2 - d_1)/2$, so firm 1's share is
--   $$
--   s(d_1, d_2) \;=\; \operatorname{clip}_{[0,1]}\!\Big(\frac{1 + d_2 - d_1}{2}\Big), \qquad \operatorname{clip}_{[0,1]}(t) = \max\{0, \min\{1, t\}\},
--   $$
--   and firm 2 serves the remaining $1 - s(d_1, d_2) = s(d_2, d_1)$.
--
--   **Pure Nash equilibrium on $[0,\infty)$.** In a two-player game where each player chooses a number $x_i \ge 0$ and receives payoff $u_i(x_1, x_2)$, a profile $(x_1, x_2)$ is a pure Nash equilibrium if $x_1, x_2 \ge 0$ and
--   $$
--   u_1(e, x_2) \le u_1(x_1, x_2) \quad\text{and}\quad u_2(x_1, e) \le u_2(x_1, x_2) \qquad \text{for every } e \ge 0 .
--   $$
--
--   These two objects are the building blocks of the platform-competition model of the mission.
--
--   **Formalization Note** The clipping is essential: without it, a firm charging a much lower disutility would get a share above $1$ and the revenue functions would become global quadratics. Ties have measure zero and play no role.
-- source:
--   Despotakis, Ravi & Srinivasan, The Beneficial Effects of Ad Blockers, SSRN 3083119 (version of Nov. 28, 2017), pp. 15–17, Sections 3.2–3.3 (Hotelling line, full coverage, p. 16; stage-2 decision variables ≥ 0, p. 14)

import Mathlib

namespace AdBlockers.Allow

/-- Clipping of a real number to the unit interval: `clip01 t = max 0 (min 1 t)`. -/
def clip01 (t : ℝ) : ℝ := max 0 (min 1 t)

/-- Hotelling duopoly with full coverage: firms sit at the endpoints `0` and `1` of the unit
interval, a consumer at position `x ∈ [0, 1]` gets `m + (1 - x) - d₁` from firm 1 and
`m + x - d₂` from firm 2, and buys from the firm giving the higher utility. Firm 1's share of a
unit mass of uniformly distributed consumers is the length of `{x ∈ [0, 1] | x < (1 + d₂ - d₁)/2}`,
i.e. `(1 + d₂ - d₁)/2` clipped to `[0, 1]`; firm 2 serves the rest. -/
noncomputable def hotellingShare (d₁ d₂ : ℝ) : ℝ := clip01 ((1 + d₂ - d₁) / 2)

/-- Pure-strategy Nash equilibrium of a two-player game whose strategy sets are both `[0, ∞)`:
player 1 has payoff `u₁ x₁ x₂`, player 2 has payoff `u₂ x₁ x₂`, and neither player gains by a
unilateral deviation to any other nonnegative strategy. -/
def IsNashNonneg (u₁ u₂ : ℝ → ℝ → ℝ) (x₁ x₂ : ℝ) : Prop :=
  0 ≤ x₁ ∧ 0 ≤ x₂ ∧
    (∀ e : ℝ, 0 ≤ e → u₁ e x₂ ≤ u₁ x₁ x₂) ∧
    (∀ e : ℝ, 0 ≤ e → u₂ x₁ e ≤ u₂ x₁ x₂)

end AdBlockers.Allow


