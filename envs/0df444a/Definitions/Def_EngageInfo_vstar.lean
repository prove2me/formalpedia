-- Prove2me | Definitions.Def_EngageInfo_vstar
-- name    : EngageInfo_vstar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:18:28.251998+00:00
-- url     : https://prove2.me/theorems/0cd85c84-9c0d-41b0-9452-737399398612
-- title:
--   The seller's equilibrium payoff $v^*(\alpha)$: the maximal SPE payoff
-- statement:
--   At a belief $\alpha$, a pure **subgame-perfect equilibrium** of the subgame is a pair $(e,P)$ of an engagement choice $e\in\{0,\bar e\}$ and a pricing rule $P:\{0,\bar e\}\to\mathbb R$ such that
--
--   1. for each engagement level $e'$ (chosen or not), $P(e')$ maximizes $S(\alpha,e',\cdot)$ over all prices;
--   2. $e$ maximizes $U(\alpha,e',P(e'))$ over $e'\in\{0,\bar e\}$.
--
--   The seller's payoff in it is $S(\alpha,e,P(e))$. The seller's equilibrium payoff is
--
--   $$v^*(\alpha)=\sup\{S(\alpha,e,P(e)) : (e,P)\text{ is a subgame-perfect equilibrium at }\alpha\}.$$
--
--   This is the function the seller concavifies when designing information.
--
--   **Formalization Note** $v^*$ is not defined by the closed form (6); (6) is a milestone, which also shows the supremum is attained. At $\alpha\in\{\alpha_0,\alpha_1,\alpha_{\bar e}\}$ there are several equilibria with different seller payoffs, and the supremum is the seller-preferred one, which is what Lemma 1 and (6) describe.
-- source:
--   Guo, Designing Information to Engage Customers, Management Science (2025), doi:10.1287/mnsc.2022.03503, §2, p.8 ("Our solution concept is subgame perfect equilibrium (SPE)"); §3.1, p.10, (6)

import Mathlib
import Definitions.Def_CollabProject_TimeDep_Game
import Definitions.Def_EngageInfo_Params
import Definitions.Def_EngageInfo_subgame

namespace EngageInfo

open CollabProject.TimeDep

/-- **The seller's equilibrium expected payoff v*(α).**
Guo, *Designing Information to Engage Customers*, Management Science (2025), §2, p.8: "Our solution
concept is subgame perfect equilibrium (SPE)"; §3.1, p.10: "It follows that the seller's equilibrium
expected payoff is v∗(α) = …" (6).

`spePayoffs M α` is the set of the seller's payoffs `S(α, e, P(e))` over all pure subgame-perfect
equilibria `(e, P)` of the subgame at belief `α`: `P` assigns a price to **each** engagement level
and is a best response after each of them (on and off the path), and `e` maximizes the customer's
payoff against `P`. `vstar M α` is the supremum of that set, the seller's payoff in the
seller-preferred equilibrium.

**Formalization Note** `v*` is **not** defined by the closed form (6); (6) is a theorem of the
mission, which also shows the supremum is attained. The paper calls the equilibrium unique (p.8),
but at `α ∈ {α₀, α₁, α_ē}` there are several SPE with different seller payoffs; the paper's
closed interval in Lemma 1 and its value in (6) are those of the seller-preferred one, hence the
supremum. -/
def spePayoffs (M : Params) (α : ℝ) : Set ℝ :=
  {x | ∃ (b : Bool) (P : Bool → ℝ), (subgame M α).IsSPNE b P ∧ x = sellerProfit M α (effort M b) (P b)}

/-- `v*(α)`: the seller's maximal subgame-perfect equilibrium payoff at belief `α`. -/
noncomputable def vstar (M : Params) (α : ℝ) : ℝ := sSup (spePayoffs M α)

end EngageInfo


