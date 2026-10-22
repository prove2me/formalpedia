-- Prove2me | Definitions.Def_TBSGStrategyIteration_IsOptimal
-- name    : TBSGStrategyIteration_IsOptimal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T00:08:32.72648+00:00
-- url     : https://prove2.me/theorems/b9e2ae56-1302-4d11-96b7-a8bbafa89570
-- title:
--   Optimal counter-strategies and optimal strategy profiles (Definitions 2.6–2.7)
-- statement:
--   Vectors are ordered componentwise: $u \le v$ iff $u_i \le v_i$ for every state $i$. A strategy $\pi_1$ of player 1 is an **optimal counter-strategy** against $\pi_2$ if
--   $$v_{\pi_1,\pi_2} \le v_{\pi_1',\pi_2} \quad \text{for every } \pi_1' \in \Pi_1,$$
--   and $\pi_2$ is an optimal counter-strategy against $\pi_1$ if $v_{\pi_1,\pi_2} \ge v_{\pi_1,\pi_2'}$ for every $\pi_2' \in \Pi_2$. These are vector inequalities: the counter-strategy must be optimal from every initial state at once. A profile $\pi = (\pi_1, \pi_2)$ is **optimal** if each of its strategies is an optimal counter-strategy against the other.
--
--   **Formalization Note.** `IsOptCounter1 G σ τ`, `IsOptCounter2 G σ τ` and `IsOptimal G π` quantify over all positional strategies and use the Pi order on `S → ℝ`.
-- source:
--   Hansen, Miltersen, Zwick, Strategy iteration is strongly polynomial for 2-player turn-based stochastic games with a constant discount factor, arXiv:1008.0530v1, p. 4, Definitions 2.6 and 2.7

import Mathlib
import Definitions.Def_TBSGStrategyIteration_value

namespace TBSGStrategyIteration

variable {S A : Type*} [Fintype S] [DecidableEq S]

/-- Def. 2.6: `π₁` is an optimal counter-strategy against `π₂` iff
`v_{π₁,π₂} ≤ v_{π₁',π₂}` (componentwise, i.e. for every initial state) for every `π₁' ∈ Π₁`. -/
def IsOptCounter1 (G : Game S A) (σ : Strat1 G) (τ : Strat2 G) : Prop :=
  ∀ σ' : Strat1 G, value G (σ, τ) ≤ value G (σ', τ)

/-- Def. 2.6: `π₂` is an optimal counter-strategy against `π₁` iff
`v_{π₁,π₂} ≥ v_{π₁,π₂'}` (componentwise) for every `π₂' ∈ Π₂`. -/
def IsOptCounter2 (G : Game S A) (σ : Strat1 G) (τ : Strat2 G) : Prop :=
  ∀ τ' : Strat2 G, value G (σ, τ') ≤ value G (σ, τ)

/-- Def. 2.7: the profile `π = (π₁, π₂)` is optimal iff `π₁` is an optimal counter-strategy
against `π₂` and `π₂` is an optimal counter-strategy against `π₁`. -/
def IsOptimal (G : Game S A) (π : Profile G) : Prop :=
  IsOptCounter1 G π.1 π.2 ∧ IsOptCounter2 G π.1 π.2

end TBSGStrategyIteration


