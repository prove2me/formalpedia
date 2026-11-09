-- Prove2me | Definitions.Def_ApproxEquilibriumCost_General_FlowCosts
-- name    : ApproxEquilibriumCost_General_FlowCosts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:47:06.044815+00:00
-- url     : https://prove2.me/theorems/583a4463-53ea-402b-aeae-e74853d80ff5
-- title:
--   §2.1 and Definition 2.1 — loads, costs, cross-cost and equilibria
-- statement:
--   For a feasible real flow $f$ in a game $G$, write $x_e(f)=\sum_{i,S:e\in S} f_{i,S}$ and $\ell_S(f)=\sum_{e\in S}\ell_e(x_e(f))$. Define
--
--   $$C(f)=\sum_e x_e(f)\ell_e(x_e(f)),\qquad C_g(g')=\sum_e x_e(g')\ell_e(x_e(g)).$$
--
--   The first cross-cost argument supplies latencies, and the second supplies traffic. A Nash equilibrium is a feasible flow whose every used strategy has minimum latency among its population's alternatives. For $\epsilon\ge0$, an approximate equilibrium is feasible and satisfies $\ell_S(f)\le(1+\epsilon)\ell_{S'}(f)$ for every used $S$ and every alternative $S'$ in the same population. Nash equilibrium reuses the published Wardrop predicate; approximate equilibrium uses the same induced loads. These observables are the common vocabulary for all cost comparisons.
-- source:
--   Yu Cheng, Tianle Jiang, STOC 2027 submission #438 (October 2026), How Much Can Approximate Equilibria Change the Social Cost of Selfish Routing?, §2.1 pp.7–8; Definition 2.1, printed p.8 = PDF p.8 (offset 0). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/438.pdf

import Mathlib
import Definitions.Def_ApproxEquilibriumCost_General_GameModel

noncomputable section

namespace ApproxEquilibriumCost.General

variable {n k : ℕ}

/-- Section 2.1, p.7: resource load, via the published incidence-weighted sum. -/
def load (G : Game n k) (f : Flow G) (e : Fin n) : ℝ :=
  KellyStochasticNetworks.linkFlow (incidence G) f e

/-- Section 2.1, p.7: the latency of an allowed subset. -/
def strategyLatency (G : Game n k) (f : Flow G) (r : Fin (routeCount G)) : ℝ :=
  ∑ e, G.latency e (load G f e) * incidence G e r

/-- Section 2.1, p.7: social cost in the resource-sum form printed in the source. -/
def cost (G : Game n k) (f : Flow G) : ℝ :=
  ∑ e, load G f e * G.latency e (load G f e)

/-- Definition 2.1, p.8: first flow supplies latencies, second supplies amounts. -/
def crossCost (G : Game n k) (g g' : Flow G) : ℝ :=
  ∑ e, load G g' e * G.latency e (load G g e)

/-- Section 2.1, p.8: the published Wardrop condition, including feasibility. -/
def IsNash (G : Game n k) (f : Flow G) : Prop :=
  KellyStochasticNetworks.IsWardropEquilibrium (incidence G) (population G)
    G.latency G.demand f

/-- Section 2.1, p.8: used subsets are within a multiplicative factor of every
alternative of the same population, evaluated at the same flow. -/
def IsApproxNash (G : Game n k) (ε : ℝ) (f : Flow G) : Prop :=
  IsFeasible G f ∧
    ∀ r r' : Fin (routeCount G), population G r' = population G r → 0 < f r →
      strategyLatency G f r ≤ (1 + ε) * strategyLatency G f r'

end ApproxEquilibriumCost.General


