-- Prove2me | Definitions.Def_SelfishRouting_Bicriteria_Model
-- name    : SelfishRouting_Bicriteria_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:10:38.008077+00:00
-- url     : https://prove2.me/theorems/9c7d1d1b-899f-457b-b1c4-011a4ae5a2ff
-- title:
--   §2.1–2.2, p. 7 — path latency $\ell_P(f)$, cost $C(f)$, and flows at Nash equilibrium (Definition 2.1)
-- statement:
--   This file sets up the nonatomic selfish-routing model of Roughgarden and Tardos (§2.1–2.2).
--
--   A network has edges $e = 1,\dots,J$ and routes $P = 1,\dots,R$. Route $P$ is the set of edges $e$ with $A_{eP} = 1$, where $A$ is a $0/1$ edge–route incidence matrix. Each route serves one commodity $s(P) \in \{1,\dots,k\}$, and $\mathcal P_i = \{P : s(P) = i\}$. A **flow** is a vector $f = (f_P)_P$; its edge flows are $f_e = \sum_{P \ni e} f_P$. It is **feasible** for the rates $r = (r_i)_i$ if $f_P \ge 0$ for every $P$ and $\sum_{P \in \mathcal P_i} f_P = r_i$ for every $i$. Each edge carries a latency function $\ell_e$.
--
--   1. The **latency of a route** is $\ell_P(f) = \sum_{e \in P} \ell_e(f_e)$.
--   2. The **cost** of a flow is
--   $$
--   C(f) = \sum_{P} \ell_P(f)\, f_P .
--   $$
--   3. The flow $\tilde f$ obtained from $f$ by moving $\delta$ units from route $P_1$ to route $P_2$ is $\tilde f_{P_1} = f_{P_1} - \delta$, $\tilde f_{P_2} = f_{P_2} + \delta$, and $\tilde f_P = f_P$ for every other route.
--   4. (**Definition 2.1**, p. 7.) The page reads: *A flow $f$ feasible for instance $(G, r, \ell)$ is at Nash equilibrium if for all $i \in \{1,\dots,k\}$, $P_1, P_2 \in \mathcal P_i$, and $\delta \in [0, f_{P_1}]$, we have $\ell_{P_1}(f) \le \ell_{P_2}(\tilde f)$.* Here: $f$ is a **Nash flow** if it is feasible for $r$ and, for every commodity $i$, every two **distinct** routes $P_1 \neq P_2$ in $\mathcal P_i$ and every $\delta$ with $0 < \delta \le f_{P_1}$,
--   $$
--   \ell_{P_1}(f) \le \ell_{P_2}(\tilde f).
--   $$
--
--   A Nash flow is one in which no infinitesimal user can lower its latency by switching routes. These objects are shared by all four missions of the series (Theorems 3.1, 4.5, 5.4 and Corollary 2.8).
--
--   **Formalization Note.** The edge flow $f_e$ and feasibility are the published `KellyStochasticNetworks.linkFlow` and `wardropFeasible`. Routes are arbitrary $0/1$ incidence columns rather than the simple $s_i$–$t_i$ paths of a graph; the paper's path family is one instance, and two copies of the same edge set serving different commodities are two routes. Two cases of the page's quantifier are excluded. (a) $P_1 = P_2$: then $\tilde f_{P_1} = f_{P_1} - \delta$ and the inequality fails at $\delta = f_{P_1} > 0$ for strictly increasing latencies, so the literal reading admits no Nash flow in most instances. (b) $\delta = 0$: then $\tilde f = f$ and the condition would force *every* route of $\mathcal P_i$, used or not, to have the same latency, which contradicts Lemma 2.2 on the same page. Both exclusions match the page's intent ("moving flow from a path to itself changes nothing", "letting $\delta$ tend to $0$").
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, pp. 6–7, §2.1 and Definition 2.1

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop

namespace SelfishRouting.Bicriteria

open KellyStochasticNetworks

/-- The latency `ℓ_P(f) = ∑_{e ∈ P} ℓ_e(f_e)` of route `r` under the route flow `x`
(Roughgarden–Tardos, p. 7). Route `r` is the set of edges `j` with `A j r = 1`, and the edge
flow `f_e` is `linkFlow A x j = ∑_r A j r * x r`. -/
def pathLatency {J R : ℕ} (A : Fin J → Fin R → ℝ) (ℓ : Fin J → ℝ → ℝ) (x : Fin R → ℝ)
    (r : Fin R) : ℝ :=
  ∑ j, ℓ j (linkFlow A x j) * A j r

/-- The cost `C(f) = ∑_{P ∈ 𝒫} ℓ_P(f) f_P` of the route flow `x` (p. 7). -/
def cost {J R : ℕ} (A : Fin J → Fin R → ℝ) (ℓ : Fin J → ℝ → ℝ) (x : Fin R → ℝ) : ℝ :=
  ∑ r, pathLatency A ℓ x r * x r

/-- The flow `f̃` of Definition 2.1: `δ` units moved from route `r₁` to route `r₂`
(`f_P − δ` on `P₁`, `f_P + δ` on `P₂`, `f_P` elsewhere). -/
def shiftFlow {R : ℕ} (x : Fin R → ℝ) (r₁ r₂ : Fin R) (δ : ℝ) : Fin R → ℝ :=
  fun r => if r = r₁ then x r - δ else if r = r₂ then x r + δ else x r

/-- **Definition 2.1** (p. 7): a route flow `x`, feasible for the rates `rate`, is at Nash
equilibrium if moving any amount `δ ∈ (0, x r₁]` of flow from a route `r₁` to another route
`r₂ ≠ r₁` of the same commodity never yields `r₂` a latency smaller than the current latency
of `r₁`: `ℓ_{P₁}(f) ≤ ℓ_{P₂}(f̃)`. The page writes `δ ∈ [0, f_{P₁}]` and does not exclude
`P₁ = P₂`; both are excluded here (see the natural-language statement). -/
def IsNashFlow {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (ℓ : Fin J → ℝ → ℝ) (rate : Fin Sd → ℝ) (x : Fin R → ℝ) : Prop :=
  x ∈ wardropFeasible s rate ∧
    ∀ r₁ r₂ : Fin R, s r₁ = s r₂ → r₁ ≠ r₂ → ∀ δ : ℝ, 0 < δ → δ ≤ x r₁ →
      pathLatency A ℓ x r₁ ≤ pathLatency A ℓ (shiftFlow x r₁ r₂ δ) r₂

end SelfishRouting.Bicriteria


