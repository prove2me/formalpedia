-- Prove2me | Definitions.Def_ApproxEquilibriumCost_General_Supplement_RoutingGame
-- name    : ApproxEquilibriumCost_General_Supplement_RoutingGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:45:33.99837+00:00
-- url     : https://prove2.me/theorems/b069e0f7-57dd-48ab-b53b-eb6efc6391b5
-- title:
--   §§2.1, 2.3 — routing games on all terminal paths
-- statement:
--   Let $N$ be a series-parallel network and let $G$ be a published nonatomic congestion game with $\operatorname{edgeCount}N$ resources and one population. The routing-game predicate is exactly
--
--   $$\mathcal S_0(G)=\operatorname{paths}(N).$$
--
--   The game already supplies an arbitrary positive real demand $r_0$ and continuous, nonnegative, nondecreasing edge latencies on $[0,\infty)$. This predicate specializes that general game by fixing all and only the terminal paths as strategies. It adds no polynomial assumption and does not normalize demand. Loads, feasible flows, costs and both equilibrium predicates remain the published operations.
-- source:
--   Yu Cheng, Tianle Jiang, STOC 2027 submission #438 (October 2026), How Much Can Approximate Equilibria Change the Social Cost of Selfish Routing?, §§2.1, 2.3, printed p.8 = PDF p.8 (offset 0). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/438.pdf

import Mathlib
import Definitions.Def_ApproxEquilibriumCost_General_GameModel
import Definitions.Def_ApproxEquilibriumCost_General_Supplement_SeriesParallel

namespace ApproxEquilibriumCost.General.Supplement

/-- Sections 2.1 and 2.3, printed/PDF pp.8–9: a single-commodity routing
game whose strategies are all and only the terminal paths of `N`.
`Game (edgeCount N) 1` supplies an arbitrary positive real demand and
continuous, nonnegative, nondecreasing edge latencies on `[0,∞)`.
No polynomial condition or unit-demand normalization is imposed.
The chosen `Fin` labelling loses no network, since resource labels can
be transported bijectively along any recursive construction. -/
def IsRoutingGame (N : SPNetwork) (G : Game (edgeCount N) 1) : Prop :=
  G.strategies 0 = paths N

end ApproxEquilibriumCost.General.Supplement


