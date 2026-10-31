-- Prove2me | Definitions.Def_PlatformCournot_IsNash
-- name    : PlatformCournot_IsNash
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:24:59.745251+00:00
-- url     : https://prove2.me/theorems/95acf87d-595f-4907-854c-35fc73c93930
-- title:
--   Definition 1 — pure strategy Nash equilibrium of the networked Cournot game
-- statement:
--   Given an edge set $\mathcal E$, the networked Cournot game is $(F,Q(\mathcal E),\pi)$. A supply profile $q\in Q(\mathcal E)$ is a **pure strategy Nash equilibrium** if for every firm $i\in F$
--
--   $$\pi_i(q_i,q_{-i})\ \ge\ \pi_i(\bar q_i,q_{-i})\qquad\text{for all }\bar q_i\in Q_i(\mathcal E).$$
--
--   **Formalization Note** This is the published generic predicate `CarbonDoubleCount.Planner.IsPureNash` (a feasible profile from which no player gains by a feasible unilateral deviation), instantiated with players `Fin n`, strategies `Fin m → ℝ`, feasible sets $Q_i(\mathcal E)$ and payoffs (8). A deviation replaces row $i$ of $q$ by $\bar q_i$.
-- source:
--   Pang, Lin, Fu, Kleeman, Bitar, Wierman, Transparency and Control in Platforms for Networked Markets, arXiv:1903.04574v3, Definition 1, p.12

import Mathlib
import Definitions.Def_CarbonDoubleCount_Planner_PureGame
import Definitions.Def_PlatformCournot_payoff
import Definitions.Def_PlatformCournot_feasibleSupply

namespace PlatformCournot

/-- **Pure strategy Nash equilibrium of the networked Cournot game, Definition 1.**
Pang et al., arXiv:1903.04574v3, Definition 1, p.12: "A supply profile q ∈ Q(ℰ) constitutes a pure
strategy Nash equilibrium of the game (F,Q(ℰ),π) if for every firm i ∈ F, it holds that
πi(qi,q−i) ≥ πi(q̄i,q−i) for all q̄i ∈ Qi(ℰ)."

`IsNash D C E q` holds when every `qᵢ ∈ Qᵢ(ℰ)` and no firm gains by a unilateral deviation to any
`q̄ᵢ ∈ Qᵢ(ℰ)`.

**Formalization Note** This is the published generic predicate
`CarbonDoubleCount.Planner.IsPureNash` with players `Fin n`, strategies `Fin m → ℝ`, feasible sets
`Qᵢ(ℰ)` and payoffs (8); a deviation is `Function.update q i q̄ᵢ`. -/
def IsNash {n m : ℕ} (D : AffineDemand m) (C : Fin n → ℝ → ℝ) (E : Set (Fin n × Fin m))
    (q : Fin n → Fin m → ℝ) : Prop :=
  CarbonDoubleCount.Planner.IsPureNash (strategy := fun _ : Fin n => Fin m → ℝ)
    (fun i => feasibleSupply E i) (fun i q' => payoff D C q' i) q

end PlatformCournot


