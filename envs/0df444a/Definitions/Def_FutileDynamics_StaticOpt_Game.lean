-- Prove2me | Definitions.Def_FutileDynamics_StaticOpt_Game
-- name    : FutileDynamics_StaticOpt_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:03.988329+00:00
-- url     : https://prove2.me/theorems/469f19fd-463c-4501-ae74-97d3d316007a
-- title:
--   §2, pp. 5–6 — repeated principal–agent game with shock and outcome spaces, utilities, and no-interaction outcome
-- statement:
--   A repeated principal–agent game has a shock space $\Theta$, an outcome space $\Omega$, and a distinguished no-interaction outcome $\emptyset\in\Omega$. The principal's utility is $u:\Theta\times\Omega\to\mathbb R$ and the agent's is $v:\Theta\times\Omega\to\mathbb R$. Both utilities vanish without interaction:
--
--   $$u(\theta,\emptyset)=v(\theta,\emptyset)=0\qquad(\theta\in\Theta).$$
--
--   This game is the reusable environment for the paper's dynamic mechanisms and regret benchmarks.
--
--   **Formalization Note** The utility functions are jointly measurable and bounded by a common finite constant. These additional conditions make the expected utilities finite and well defined.
-- source:
--   Balseiro, Kim & Russo, On the futility of dynamics in robust mechanism design, SSRN 3449698 (version of October 5, 2020), pp. 5–6, §2 game and no-interaction outcome

import Mathlib

namespace FutileDynamics.StaticOpt

open MeasureTheory

/-- The environment `(Ω, Θ, u, v)` with the no-interaction outcome `∅` (Balseiro–Kim–Russo, §2, p. 5):
`u θ ω` is the principal's and `v θ ω` the agent's utility when the shock is `θ` and the outcome `ω`.
Both utilities vanish at `∅ = noInt` (p. 6). Disclosed conventions (not on the page): `u` and `v` are jointly
measurable and bounded by a common constant `B`, so that every expected utility below is a genuine finite
integral. -/
structure Game (Θ Ω : Type) [MeasurableSpace Θ] [MeasurableSpace Ω] where
  /-- principal's utility `u : Θ × Ω → ℝ` -/
  u : Θ → Ω → ℝ
  /-- agent's utility `v : Θ × Ω → ℝ` -/
  v : Θ → Ω → ℝ
  /-- the no-interaction outcome `∅ ∈ Ω` -/
  noInt : Ω
  u_noInt : ∀ θ, u θ noInt = 0
  v_noInt : ∀ θ, v θ noInt = 0
  u_meas : Measurable (Function.uncurry u)
  v_meas : Measurable (Function.uncurry v)
  bdd : ∃ B : ℝ, ∀ θ ω, |u θ ω| ≤ B ∧ |v θ ω| ≤ B

end FutileDynamics.StaticOpt


