-- Prove2me | Definitions.Def_EngageInfo_subgame
-- name    : EngageInfo_subgame
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:40.030048+00:00
-- url     : https://prove2.me/theorems/313a4aee-ac49-47ac-ab61-fb23711079c9
-- title:
--   The engagement–pricing subgame at belief $\alpha$: profit $S(\alpha,e,p)$, customer payoff $U(\alpha,e,p)$
-- statement:
--   Fix a common belief $\alpha$ that the state is $H$. The customer first chooses whether to engage ($e=\bar e$ at cost $k$) or not ($e=0$). The seller observes $e$ and sets a price $p$. The customer then learns the state $\omega$ and buys if and only if $\theta_\omega+e-p\ge 0$. Hence the seller's expected profit and the customer's expected payoff are
--
--   $$S(\alpha,e,p)=(p-c)\Bigl(\alpha\,\mathbf 1[p\le\theta_H+e]+(1-\alpha)\,\mathbf 1[p\le\theta_L+e]\Bigr),$$
--
--   $$U(\alpha,e,p)=\alpha\max\{\theta_H+e-p,0\}+(1-\alpha)\max\{\theta_L+e-p,0\}-k\,\mathbf 1[e=\bar e].$$
--
--   The subgame is the two-stage game in which the customer (the first mover) chooses $e$ and the seller (the second mover) chooses $p$, with these payoffs.
--
--   This is the second-stage subgame of the paper whose equilibrium payoff $v^*(\alpha)$ the seller's information design acts on.
--
--   **Formalization Note** Engagement is a Boolean (`true` for $\bar e$). The game is an instance of the published two-stage `SequentialGame`. The customer buys at indifference; the paper leaves this implicit, and without it the seller has no best price.
-- source:
--   Guo, Designing Information to Engage Customers, Management Science (2025), doi:10.1287/mnsc.2022.03503, (1), p.6; engagement, p.7; timing and Stage 4, pp.7–8 (Figure 1); observable engagement, §3, p.9

import Mathlib
import Definitions.Def_CollabProject_TimeDep_Game
import Definitions.Def_EngageInfo_Params

namespace EngageInfo

open CollabProject.TimeDep

/-- **The engagement–pricing subgame at a common belief α (observable engagement).**
Guo, *Designing Information to Engage Customers*, Management Science (2025), §2, pp.6–8 (payoff (1),
Figure 1) and §3, p.9. (1), p.6: "the customer has a single-unit demand, whose (ex post) net payoff of
purchase is u = θω + e − p". p.8: "at the beginning of the last stage, the true state ω is revealed to
the customer but not to the seller". §3: the seller sets the price after observing the customer's
engagement `e ∈ {0, ē}` (p.7), which costs the customer `k` when `e = ē`.

At belief `α` (the probability of the state H), the customer moves first and chooses whether to
engage (`true` means `e = ē`, `false` means `e = 0`); the seller observes the choice and sets a price
`p`; the customer then learns the state `ω` and buys iff `θ_ω + e − p ≥ 0`. Hence

* the seller's expected profit is `S(α, e, p) = (p − c)(α·[p ≤ θ_H + e] + (1 − α)·[p ≤ θ_L + e])`;
* the customer's expected payoff is
  `U(α, e, p) = α·max(θ_H + e − p, 0) + (1 − α)·max(θ_L + e − p, 0) − (k if e = ē else 0)`.

`subgame M α` packages these as a two-stage sequential game (the published
`CollabProject.TimeDep.SequentialGame`): player 1 (the customer) chooses engagement in `Bool`, player 0
(the seller) observes it and chooses a price in `ℝ`.

**Formalization Note** Engagement is encoded by `Bool` (`effort M true = ē`, `effort M false = 0`).
The customer buys at indifference (`θ_ω + e − p ≥ 0`): the paper leaves this implicit, and without
it the seller has no best price. The stage-4 purchase decision is folded into the payoffs, and the
engagement cost is sunk by then, so it does not affect the purchase. Strategies are pure. -/
def effort (M : Params) (b : Bool) : ℝ := if b then M.ebar else 0

/-- The customer's engagement cost: `k` if engaged, `0` otherwise. -/
def engageCost (M : Params) (b : Bool) : ℝ := if b then M.k else 0

/-- The seller's expected profit `S(α, e, p)` from price `p` after engagement level `e`, at belief
`α`: the customer buys in state ω iff `p ≤ θ_ω + e`. -/
noncomputable def sellerProfit (M : Params) (α e p : ℝ) : ℝ :=
  (p - M.c) * (α * (if p ≤ M.θH + e then 1 else 0) + (1 - α) * (if p ≤ M.θL + e then 1 else 0))

/-- The customer's expected payoff `U(α, e, p)` from engagement choice `b` and price `p`, at belief
`α`, net of the engagement cost. -/
noncomputable def customerPayoff (M : Params) (α : ℝ) (b : Bool) (p : ℝ) : ℝ :=
  α * max (M.θH + effort M b - p) 0 + (1 - α) * max (M.θL + effort M b - p) 0 - engageCost M b

/-- The subgame at belief `α`: the customer (player 1) chooses engagement, the seller (player 0)
observes it and sets the price. -/
noncomputable def subgame (M : Params) (α : ℝ) : SequentialGame Bool ℝ where
  payoff1 := fun b p => customerPayoff M α b p
  payoff0 := fun b p => sellerProfit M α (effort M b) p

end EngageInfo


