-- Prove2me | Definitions.Def_SelfishRouting_Linear_Model
-- name    : SelfishRouting_Linear_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:15:21.989602+00:00
-- url     : https://prove2.me/theorems/7d4b14e4-95d6-4a4e-8527-a79e724683a2
-- title:
--   Route flows, path latency $\ell_P(f)$, cost $C(f)$, Nash flows (Definition 2.1) and optimal flows
-- statement:
--   This module sets up the nonatomic routing model of Roughgarden and Tardos (§2.1–2.3).
--
--   A network has finitely many edges $e$ and finitely many routes $P$; route $P$ is the set of edges $e$ with incidence $A_{eP}=1$ (the incidence is $0$ or $1$). There are $k$ commodities (source–destination pairs); each route serves exactly one commodity $i$, and $\mathcal P_i$ denotes the routes serving $i$. Commodity $i$ has a rate $r_i$. A **flow** assigns an amount $f_P$ to every route; it is **feasible** for the rates $r$ if $f_P\ge 0$ for all $P$ and $\sum_{P\in\mathcal P_i} f_P=r_i$ for every $i$. The flow on edge $e$ is $f_e=\sum_{P} A_{eP} f_P$. Each edge carries a latency function $\ell_e$.
--
--   1. The **latency of a path** is $\ell_P(f)=\sum_{e\in P}\ell_e(f_e)$.
--   2. The **cost** of a flow is
--   $$C(f)=\sum_{P\in\mathcal P}\ell_P(f)\,f_P .$$
--   3. A feasible flow $f$ is **at Nash equilibrium** (Definition 2.1, p. 7) if for every commodity $i$, every two distinct routes $P_1\neq P_2$ in $\mathcal P_i$ and every $\delta$ with $0<\delta\le f_{P_1}$,
--   $$\ell_{P_1}(f)\le \ell_{P_2}(\tilde f),\qquad \tilde f_P=\begin{cases} f_P-\delta & P=P_1,\\ f_P+\delta & P=P_2,\\ f_P & P\notin\{P_1,P_2\},\end{cases}$$
--   that is, no infinitesimal part of the flow on $P_1$ can lower its latency by moving to $P_2$.
--   4. A flow is **optimal** for the rates $r$ (§2.3, p. 8: "a flow that minimizes total latency") if it is feasible and $C(f)\le C(g)$ for every feasible flow $g$.
--
--   The paper's Definition 2.1 reads: "A flow f feasible for instance (G, r, ℓ) is at Nash equilibrium if for all i ∈ {1, . . . , k}, P₁, P₂ ∈ 𝒫ᵢ, and δ ∈ [0, f_{P₁}], we have ℓ_{P₁}(f) ≤ ℓ_{P₂}(f̃)", with f̃ as above.
--
--   **Formalization Note** Two literal readings of Definition 2.1 are degenerate and are excluded. (i) $P_1=P_2$: then $\tilde f_{P_1}=f_{P_1}-\delta$ and the inequality fails for any strictly increasing latency at $\delta=f_{P_1}>0$, so Nash flows would not exist; the definition requires $P_1\neq P_2$ (moving flow from a path to itself changes nothing). (ii) $\delta=0$ with $f_{P_1}=0$: then the condition would demand $\ell_{P_1}(f)\le\ell_{P_2}(f)$ also for *unused* $P_1$, which the Wardrop flow $(0,1)$ on two parallel links with latencies $2$ and $x$ violates; the definition takes $\delta\in(0,f_{P_1}]$, which is the reading under which the paper's Lemma 2.2 ("letting δ tend to 0") holds. Routes are arbitrary $0/1$ incidence columns rather than simple paths of a directed graph; the paper's simple-path family is one instance, so every theorem stated over this model is a (disclosed) generalization. Copies of one path serving two commodities are two routes. Feasibility uses the published `KellyStochasticNetworks.wardropFeasible` and edge flows `KellyStochasticNetworks.linkFlow`.
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, pp. 6–8, §2.1 (model, C(f)), Definition 2.1 (p. 7), §2.3 (optimal flow, p. 8)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Bicriteria_Model

namespace SelfishRouting.Linear

open KellyStochasticNetworks

/-- **Optimal flow** (§2.3, p. 8: "a flow that minimizes total latency"): a feasible flow whose
cost is at most the cost of every feasible flow for the same rates. -/
def IsOptimalFlow {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (ℓ : Fin J → ℝ → ℝ) (rate : Fin Sd → ℝ) (x : Fin R → ℝ) : Prop :=
  x ∈ wardropFeasible s rate ∧ ∀ y ∈ wardropFeasible s rate, SelfishRouting.Bicriteria.cost A ℓ x ≤ SelfishRouting.Bicriteria.cost A ℓ y

end SelfishRouting.Linear


