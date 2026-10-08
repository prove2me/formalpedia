-- Prove2me | Definitions.Def_SelfishRouting_Potential_Model
-- name    : SelfishRouting_Potential_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:15:29.869299+00:00
-- url     : https://prove2.me/theorems/382b9725-747b-4cf9-8f24-280d1acf5b76
-- title:
--   Nonatomic selfish routing: path latency $\ell_P(f)$, cost $C(f)$ and flows at Nash equilibrium (Definition 2.1)
-- statement:
--   This is the network model of Roughgarden and Tardos, *How Bad is Selfish Routing?*, §2.1–2.2.
--
--   A network has finitely many edges $e$ and finitely many routes $P$. Route $P$ is described by its column of a $0/1$ edge–route incidence matrix $A$ ($A_{eP}=1$ when $e\in P$), and each route serves one of the commodities $i\in\{1,\dots,k\}$, i.e. one source–destination pair $\{s_i,t_i\}$; $\mathcal P_i$ is the set of routes serving commodity $i$. Commodity $i$ has a rate $r_i$. A **flow** assigns to each route a value $f_P$; it induces the edge flows $f_e=\sum_{P\ni e} f_P$, and it is **feasible** when $f_P\ge 0$ for every route and $\sum_{P\in\mathcal P_i} f_P=r_i$ for every commodity. These two objects (edge flow and feasibility) are taken from the published definition `KellyStochasticNetworks_Wardrop`. Each edge carries a latency function $\ell_e$.
--
--   1. The **latency of a route** is the sum of its edge latencies,
--   $$\ell_P(f)=\sum_{e\in P}\ell_e(f_e).$$
--   2. The **cost** of a flow is its total latency,
--   $$C(f)=\sum_{P}\ell_P(f)\,f_P .$$
--   3. For routes $P_1,P_2$ and $\delta\ge 0$, the flow $\tilde f$ moves $\delta$ units from $P_1$ to $P_2$:
--   $$\tilde f_P=\begin{cases} f_P-\delta & P=P_1,\\ f_P+\delta & P=P_2,\\ f_P & P\notin\{P_1,P_2\}.\end{cases}$$
--   4. **Definition 2.1** (p. 7) reads: "A flow $f$ feasible for instance $(G,r,\ell)$ is at Nash equilibrium if for all $i\in\{1,\dots,k\}$, $P_1,P_2\in\mathcal P_i$, and $\delta\in[0,f_{P_1}]$, we have $\ell_{P_1}(f)\le\ell_{P_2}(\tilde f)$." Here a feasible flow $f$ is **at Nash equilibrium** when, for every commodity $i$, all **distinct** routes $P_1\ne P_2$ in $\mathcal P_i$ with $f_{P_1}>0$, and every $\delta\in[0,f_{P_1}]$,
--   $$\ell_{P_1}(f)\le\ell_{P_2}(\tilde f).$$
--
--   The definition expresses that no infinitesimal part of the traffic can lower its latency by switching routes. It is the object of every efficiency bound in the paper.
--
--   **Formalization Note** Two guards are added to the printed condition, each excluding a case in which it reads differently from its intent. (a) $P_1\ne P_2$: when $P_1=P_2$ the printed case split gives $\tilde f_{P_1}=f_{P_1}-\delta$, and the condition would fail for every strictly increasing latency, so Nash flows would not exist. (b) $f_{P_1}>0$: when $f_{P_1}=0$ the only admissible $\delta$ is $0$, $\tilde f=f$, and the printed condition would force every route of commodity $i$, used or not, to have the same latency, contradicting Lemma 2.2. With both guards the definition is equivalent to Lemma 2.2's characterization under continuous nondecreasing latencies. Routes are arbitrary $0/1$ incidence columns rather than simple paths of a graph, a generalization the paper's arguments never use; two copies of one path serving two commodities are two routes. Edges, routes and commodities are `Fin J`, `Fin R`, `Fin Sd`.
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, pp. 6-7, Section 2.1 and Definition 2.1

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Bicriteria_Model

namespace SelfishRouting.Potential

open KellyStochasticNetworks

/-- **Flow at Nash equilibrium**, Definition 2.1 (p. 7): a route flow `x` feasible for the
rates `rate` such that, for any two distinct routes `r₁ ≠ r₂` serving the same commodity with
`x r₁ > 0` and any `δ ∈ [0, x r₁]`, the latency of `r₁` under `x` is at most the latency of
`r₂` after `δ` units have been moved from `r₁` to `r₂`.  The guards `r₁ ≠ r₂` and `x r₁ > 0`
exclude the two cases in which the printed condition degenerates (see the item's description). -/
def IsNashFlow {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (ℓ : Fin J → ℝ → ℝ) (rate : Fin Sd → ℝ) (x : Fin R → ℝ) : Prop :=
  x ∈ wardropFeasible s rate ∧
    ∀ r₁ r₂ : Fin R, s r₁ = s r₂ → r₁ ≠ r₂ → 0 < x r₁ →
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ x r₁ →
        SelfishRouting.Bicriteria.pathLatency A ℓ x r₁ ≤ SelfishRouting.Bicriteria.pathLatency A ℓ (SelfishRouting.Bicriteria.shiftFlow x r₁ r₂ δ) r₂

end SelfishRouting.Potential


