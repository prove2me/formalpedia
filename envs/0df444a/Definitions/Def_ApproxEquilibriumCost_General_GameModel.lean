-- Prove2me | Definitions.Def_ApproxEquilibriumCost_General_GameModel
-- name    : ApproxEquilibriumCost_General_GameModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:35.637059+00:00
-- url     : https://prove2.me/theorems/1fbe0641-00f3-4cac-a41e-7b10ad752027
-- title:
--   §2.1 — general nonatomic congestion games and feasible real flows
-- statement:
--   A game has finite resource and population sets $E,K$, positive real demands $r_i$, and a nonempty family $\mathcal S_i\subseteq 2^E$ for each population. Each latency $\ell_e$ is continuous, nonnegative and nondecreasing on $[0,\infty)$. An allowed strategy may be empty. A real flow assigns amounts to allowed population-strategy pairs; feasibility means
--
--   $$f_{i,S}\ge0,\qquad \sum_{S\in\mathcal S_i}f_{i,S}=r_i.$$
--
--   The definition provides a bijective finite enumeration and its $0/1$ incidence matrix. Feasibility reuses the published Wardrop interface. This generic game layer contains no polynomial condition, equilibrium estimate or cost lower bound. Finite relabeling changes no instance or traffic amount.
-- source:
--   Yu Cheng, Tianle Jiang, STOC 2027 submission #438 (October 2026), How Much Can Approximate Equilibria Change the Social Cost of Selfish Routing?, §2.1 (continued p.8), printed p.7 = PDF p.7 (offset 0). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/438.pdf

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop

noncomputable section

namespace ApproxEquilibriumCost.General

/-- Section 2.1, printed/PDF pp.7–8. Finite sets are relabeled by `Fin`; no
nonemptiness of the resource or population type is imposed. -/
structure Game (n k : ℕ) where
  strategies : Fin k → Finset (Finset (Fin n))
  strategies_nonempty : ∀ i, (strategies i).Nonempty
  demand : Fin k → ℝ
  demand_pos : ∀ i, 0 < demand i
  latency : Fin n → ℝ → ℝ
  latency_continuous : ∀ e, ContinuousOn (latency e) (Set.Ici 0)
  latency_nonnegative : ∀ e x, 0 ≤ x → 0 ≤ latency e x
  latency_monotone : ∀ e, MonotoneOn (latency e) (Set.Ici 0)

variable {n k : ℕ}

/-- One coordinate for each population and allowed subset, including an empty subset. -/
abbrev StrategyIndex (G : Game n k) := Σ i : Fin k, {S // S ∈ G.strategies i}

/-- The number of allowed population-strategy pairs, with no traffic discretization. -/
def routeCount (G : Game n k) : ℕ := Fintype.card (StrategyIndex G)

/-- A bijective enumeration, used only to access the published finite Wardrop API. -/
def route (G : Game n k) (r : Fin (routeCount G)) : StrategyIndex G :=
  (Fintype.equivFin (StrategyIndex G)).symm r

def population (G : Game n k) (r : Fin (routeCount G)) : Fin k := (route G r).1

/-- Incidence of a resource in an allowed subset, always zero or one. -/
def incidence (G : Game n k) (e : Fin n) (r : Fin (routeCount G)) : ℝ :=
  if e ∈ (route G r).2.val then 1 else 0

/-- Real amounts on all and only the allowed population-strategy pairs. -/
abbrev Flow (G : Game n k) := Fin (routeCount G) → ℝ

/-- Feasibility uses the published nonnegative flow and exact demand constraints. -/
def IsFeasible (G : Game n k) (f : Flow G) : Prop :=
  f ∈ KellyStochasticNetworks.wardropFeasible (population G) G.demand

end ApproxEquilibriumCost.General


