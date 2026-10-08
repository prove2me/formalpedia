-- Prove2me | Definitions.Def_SelfishRouting_Splittable_Model
-- name    : SelfishRouting_Splittable_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:15:31.802935+00:00
-- url     : https://prove2.me/theorems/ace5d7d1-dfeb-417d-92ef-a967a74f8e33
-- title:
--   Finite splittable selfish routing: path latency, cost $C(f)$, agent cost $C_i(f)$ and Nash equilibrium
-- statement:
--   This definition fixes the model of **selfish routing with finitely many agents who may split their flow** (Roughgarden–Tardos, §2.1 and §5.2).
--
--   There is a finite set of edges $e = 1,\dots,J$, a finite set of routes $r = 1,\dots,R$, and $k$ agents $i = 1,\dots,k$. Route $r$ is described by its incidence column $A_{e r}\in\{0,1\}$ (the route uses edge $e$ iff $A_{er}=1$), and it belongs to exactly one agent $s(r)$; the routes of agent $i$ form the set $\mathcal P_i = \{r : s(r) = i\}$. Agent $i$ must send $r_i>0$ units of flow. A **flow** is a vector $f = (f_P)_P$ of route flows; agent $i$'s part $f^{(i)}$ is its restriction to $\mathcal P_i$. The flow is **feasible** if $f_P\ge 0$ for every route and $\sum_{P\in\mathcal P_i} f_P = r_i$ for every agent. The **edge flow** is the total flow of all agents through the edge, $f_e = \sum_P A_{eP} f_P$. Each edge carries a latency function $\ell_e$.
--
--   1. The **path latency** is $\ell_P(f) = \sum_{e\in P}\ell_e(f_e)$.
--   2. The **cost** of a flow is its total latency
--   $$C(f) = \sum_{P}\ell_P(f)\,f_P .$$
--   3. The **cost of agent $i$** is $C_i(f) = \sum_{P\in\mathcal P_i}\ell_P(f)\,f^{(i)}_P$: agent $i$ pays for its own flow only, but at latencies determined by the flow of all agents.
--   4. A feasible flow $f$ is **at Nash equilibrium** if for each agent $i$, $f^{(i)}$ minimizes $C_i(f)$ given $f^{(j)}$ for $j\ne i$: for every feasible flow $g$ that coincides with $f$ on the routes of every other agent,
--   $$C_i(f)\le C_i(g).$$
--
--   Every theorem of this mission is stated in this model.
--
--   **Formalization Note** Routes are arbitrary $0/1$ incidence columns rather than the simple $s_i$–$t_i$ paths of a graph, a disclosed generalization: the paper's path families are one instance. Two agents with the same source and destination have separate copies of every path, which is the page's "one function $f^{(i)}:\mathcal P_i\to\mathcal R^+$ for each agent $i$". Edges, routes and agents are indexed by `Fin J`, `Fin R`, `Fin Sd`; the edge flow and the feasible set are `linkFlow` and `wardropFeasible` of the published definition `KellyStochasticNetworks_Wardrop`. The page's "if and only if" characterization of a Nash flow is taken as the definition.
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, pp. 6–7, §2.1 (ℓ_P(f), C(f)); p. 19, §5.2 (finite splittable instance, C_i(f), Nash equilibrium)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Bicriteria_Model

namespace SelfishRouting.Splittable

open KellyStochasticNetworks

/-- The total latency `C_i(f) = ∑_{P ∈ 𝒫_i} ℓ_P(f) f^{(i)}_P` experienced by agent `i`: the routes
of agent `i` are those with `s r = i`, and their latencies are evaluated at the edge flows of all
agents together.  §5.2, p. 19. -/
def agentCost {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (ℓ : Fin J → ℝ → ℝ) (x : Fin R → ℝ) (i : Fin Sd) : ℝ :=
  ∑ r ∈ Finset.univ.filter (fun r => s r = i), SelfishRouting.Bicriteria.pathLatency A ℓ x r * x r

/-- A flow at Nash equilibrium for a finite splittable instance (§5.2, p. 19): `x` is feasible
(each agent `i` sends exactly `rate i` over its own routes), and for every agent `i`, the
restriction of `x` to agent `i`'s routes minimizes `C_i` among all feasible flows that agree
with `x` on the routes of every other agent ("`f^{(i)}` minimizes `C_i(f)` given `f^{(j)}` for
`j ≠ i`"). -/
def IsSplittableNash {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (ℓ : Fin J → ℝ → ℝ) (rate : Fin Sd → ℝ) (x : Fin R → ℝ) : Prop :=
  x ∈ wardropFeasible s rate ∧
    ∀ i : Fin Sd, ∀ y ∈ wardropFeasible s rate, (∀ r, s r ≠ i → y r = x r) →
      agentCost A s ℓ x i ≤ agentCost A s ℓ y i

end SelfishRouting.Splittable


