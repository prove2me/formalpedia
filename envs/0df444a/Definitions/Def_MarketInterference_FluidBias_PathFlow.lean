-- Prove2me | Definitions.Def_MarketInterference_FluidBias_PathFlow
-- name    : MarketInterference_FluidBias_PathFlow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:29.102774+00:00
-- url     : https://prove2.me/theorems/908c4953-98c2-40a0-be07-4fc50726698d
-- title:
--   pp. 9–10 — supply-to-demand paths, path values ν_{i,j,p} and path decompositions of an arc flow
-- statement:
--   In a matching network, a **supply-to-demand path** from the supply node $u^s_j$ to the demand node $u^d_i$ is a sequence of distinct arcs that starts at $u^s_j$, ends at $u^d_i$, and passes only through intermediate nodes in between. Its edge set is denoted $\mathcal A_{i,j,p}\subseteq\mathcal A$, and one unit of demand of type $i$ matched to supply of type $j$ along $p$ creates the value
--   $$
--   \nu_{i,j,p}=\sum_{(u,w)\in\mathcal A_{i,j,p}}v_{u,w}.
--   $$
--
--   A **path decomposition** of an arc flow $x$ is a family of nonnegative path flows $y_{i,j,p}$, finitely many of them nonzero, whose arc totals reproduce $x$: for every arc $e$,
--   $$
--   \sum_{p\ni e}y_{p}=x_e .
--   $$
--   The quantity $y^*_{i,j,p}$ of (10), "the number of demand units of type $i$ matched to supply units of type $j$ along path $p$ in the optimal solution", is such a decomposition of the optimal arc flow.
--
--   **Formalization Note.** A path is a nonempty list of pairwise distinct arcs (`List.Nodup`) whose first arc has tail `Sum.inl j`, whose last arc has head `Sum.inl i`, and whose consecutive arcs meet at an intermediate node (`List.IsChain`); the endpoint types $i$, $j$ are recorded in the structure `SDPath`. Since the arcs are distinct, an arc occurs in a path $0$ or $1$ times, and the decomposition condition is written with `List.count`. With intermediate nodes an optimal flow has in general several decompositions; the theorems of this mission quantify over every one of them. A flow with a circulating part inside the intermediate nodes has no decomposition.
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, pp. 9–10 (paths, n_{i,j}, ν_{i,j,p}, 𝒜_{i,j,p}); p. 13, (10)

import Mathlib
import Definitions.Def_MarketInterference_FluidBias_NetworkLP

namespace MarketInterference.FluidBias

variable {nd ns : ℕ} {I E : Type}

/-- A supply-to-demand path of the network `N` (pp. 9–10): a nonempty list of pairwise distinct
arcs whose first arc leaves the supply node `u^s_j`, whose last arc enters the demand node
`u^d_i`, and in which each arc ends at the intermediate node where the next arc starts. The
endpoints `i` (demand type) and `j` (supply type) are recorded. -/
structure SDPath (N : Network nd ns I E) where
  /-- the demand type at the end of the path -/
  i : Fin nd
  /-- the supply type at the start of the path -/
  j : Fin ns
  /-- the arcs of the path, in order -/
  arcs : List E
  ne_nil : arcs ≠ []
  nodup : arcs.Nodup
  first_tail : ∀ e ∈ arcs.head?, N.tail e = Sum.inl j
  last_head : ∀ e ∈ arcs.getLast?, N.head e = Sum.inl i
  chain : arcs.IsChain (fun e f => ∃ u : I, N.head e = Sum.inr u ∧ N.tail f = Sum.inr u)

/-- The value `ν_{i,j,p} = ∑_{(u,w) ∈ 𝒜_{i,j,p}} v_{u,w}` of one unit of flow along the path. -/
def pathValue {N : Network nd ns I E} (p : SDPath N) : ℝ := (p.arcs.map N.v).sum

/-- `y` is a path decomposition of the arc flow `x`: a finitely supported nonnegative flow on
supply-to-demand paths whose arc totals are `x`, i.e. for every arc `e`,
`∑_p y_p · [e ∈ p] = x_e` (the paths have distinct arcs, so `count` is `0` or `1`). -/
def IsPathDecomposition [DecidableEq E] (N : Network nd ns I E) (y : SDPath N →₀ ℝ)
    (x : E → ℝ) : Prop :=
  (∀ p, 0 ≤ y p) ∧ ∀ e, ∑ p ∈ y.support, y p * (p.arcs.count e : ℝ) = x e

end MarketInterference.FluidBias


