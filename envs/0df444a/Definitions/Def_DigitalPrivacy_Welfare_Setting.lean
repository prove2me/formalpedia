-- Prove2me | Definitions.Def_DigitalPrivacy_Welfare_Setting
-- name    : DigitalPrivacy_Welfare_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:32:15.837207+00:00
-- url     : https://prove2.me/theorems/fe1cb27f-b5cd-4519-b6b8-87d4019840ee
-- title:
--   §2, §3, §5 — equilibrium activity ā* (3), consumer surplus (4), profit Π (2), welfare W (7), feasible strategies, business and social optima
-- statement:
--   This file fixes the model of Fainmesser, Galeotti and Momot's *Digital Privacy* that is needed to compare a digital business's data strategy with the socially optimal one.
--
--   **Parameters.** All parameters are real numbers: the network effect $\beta\in[0,1)$, the users' marginal benefit from stored data $\rho\in[0,1)$, the unit cost of data protection $\psi$, the business's revenue model $P\in[0,1]$ ($P=0$ is purely usage-driven, $P=1$ purely data-driven), and the planner's weight $\alpha\in[0,1]$ on consumer surplus.
--
--   **Data strategies.** A data strategy is a pair $(\xi,C)$: the share $\xi\in[0,1]$ of each user's activity that the business stores, and the protection level $C\ge 0$. The set of such pairs is the **feasible set** $[0,1]\times[0,\infty)$.
--
--   **Equilibrium activity** (Proposition 1, display (3)). Given $(\xi,C)$, users and adversaries play a subgame whose equilibrium average user activity is
--   $$
--   \bar a^*(\xi,C)=\frac{C(1+\rho\xi)}{C(1-\beta)+\xi^2}\qquad(\xi\neq 0),\qquad \bar a^*(0,C)=\frac{1}{1-\beta}.
--   $$
--   The value at $\xi=0$ is the users' activity when nothing is stored; it agrees with (3) for every $C>0$ and is the value the paper uses at $(\xi,C)=(0,0)$, where (3) reads $0/0$.
--
--   **Payoffs.** Consumer surplus (4), the business's profit (2) and the planner's objective (7) are
--   $$
--   \mathrm{CS}(\xi,C)=\tfrac12\,\bar a^*(\xi,C)^2,\qquad
--   \Pi(\xi,C)=(1-P)\,\bar a^*(\xi,C)+P\,\xi\,\bar a^*(\xi,C)-\psi C,\qquad
--   W(\xi,C)=\alpha\,\mathrm{CS}(\xi,C)+(1-\alpha)\,\Pi(\xi,C).
--   $$
--
--   **Optima.** A *business optimum* $(\xi^*,C^*)$ is a feasible strategy with $\Pi(\xi',C')\le\Pi(\xi^*,C^*)$ for every feasible $(\xi',C')$; a *social optimum* $(\xi^W,C^W)$ is a feasible strategy maximizing $W$ over the feasible set in the same sense (problem (7)). Neither is assumed unique.
--
--   **Parameter ranges.** *PrintedBounds* collects the ranges printed in the paper: $0\le\beta<1$, $0\le\rho<1$, $\psi\ge0$, $0\le P\le1$, $0\le\alpha\le1$. *Standing* adds $\psi>0$ and $\alpha>0$.
--
--   The equilibrium activity $\bar a^*$, the consumer surplus, the feasible set and the business optimum are imported from the shared module *DigitalPrivacy.Strategy.Setting* (`abar`, `CS`, `Feasible`, `IsBusinessOpt`, the last maximizing `profit`, the same expression as $\Pi$ here); this file adds $\Pi$, $W$, the social optimum and the parameter ranges.
--
--   These objects are shared by every statement of the mission: Theorem 2, displays (11)–(12), Proposition 5(i) and the purely usage-driven step of the proof of Theorem 2.
--
--   **Formalization Note.** The parameters are explicit real arguments of every object. The value $\bar a^*(0,C)=1/(1-\beta)$ replaces the indeterminate $0/0$ of (3) at $C=0$, following the paper's own use (App. A.2, p. 30, $\pi_0=(1-P)/(1-\beta)$; App. A.3, p. 32, $\bar a_c=1/(1-\beta)$); Lean's default $0/0=0$ would change which strategies are optimal. The two additions in *Standing* are disclosed: $\psi>0$ because with $\psi=0$ the profit has no maximizer in general and the purely usage-driven statement fails at $\rho=0$; $\alpha>0$ because the paper's step (11) needs positive weight on consumer surplus.
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (This Draft: April 2022; SSRN 3459274), pp. 6–8 (§2, (1)–(2)), p. 10 (Proposition 1, (3)–(4)), p. 13 ((7)); value at ξ = 0 from App. A.2, p. 30 and App. A.3, p. 32

import Mathlib
import Definitions.Def_DigitalPrivacy_Strategy_Setting

namespace DigitalPrivacy.Welfare

/-- The business's profit (2): `Π(ξ, C) = (1 - P) ā* + P ξ ā* - ψ C` (the same expression as
`DigitalPrivacy.Strategy.profit`, which `IsBusinessOpt` maximizes). -/
noncomputable def Pi (β ρ ψ P ξ C : ℝ) : ℝ :=
  (1 - P) * DigitalPrivacy.Strategy.abar β ρ ξ C + P * (ξ * DigitalPrivacy.Strategy.abar β ρ ξ C) - ψ * C

/-- The planner's objective (7): `W(ξ, C) = α CS(ξ, C) + (1 - α) Π(ξ, C)`, with `CS` the consumer
surplus (4) of `DigitalPrivacy.Strategy`. -/
noncomputable def W (β ρ ψ P α ξ C : ℝ) : ℝ :=
  α * DigitalPrivacy.Strategy.CS β ρ ξ C + (1 - α) * Pi β ρ ψ P ξ C

/-- `(ξ, C)` is a social optimum, a solution of (7): a feasible strategy maximizing `W` over all
feasible strategies. -/
def IsSocialOpt (β ρ ψ P α ξ C : ℝ) : Prop :=
  DigitalPrivacy.Strategy.Feasible ξ C ∧ ∀ ξ' C', DigitalPrivacy.Strategy.Feasible ξ' C' → W β ρ ψ P α ξ' C' ≤ W β ρ ψ P α ξ C

/-- The parameter ranges printed in the paper: `β ∈ [0, 1)`, `ρ ∈ [0, 1)` (p. 6), `ψ ≥ 0`,
`P ∈ [0, 1]` (p. 8), `α ∈ [0, 1]` (p. 13). -/
def PrintedBounds (β ρ ψ P α : ℝ) : Prop :=
  0 ≤ β ∧ β < 1 ∧ 0 ≤ ρ ∧ ρ < 1 ∧ 0 ≤ ψ ∧ 0 ≤ P ∧ P ≤ 1 ∧ 0 ≤ α ∧ α ≤ 1

/-- The standing assumptions of Theorem 2: the printed ranges, strengthened to `ψ > 0`
(the cost of protection is positive) and `α > 0` (the planner puts positive weight on
consumer surplus). -/
def Standing (β ρ ψ P α : ℝ) : Prop :=
  PrintedBounds β ρ ψ P α ∧ 0 < ψ ∧ 0 < α

end DigitalPrivacy.Welfare


