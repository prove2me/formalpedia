-- Prove2me | Definitions.Def_MulticastPoS_game
-- name    : MulticastPoS_game
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:39:38.743518+00:00
-- url     : https://prove2.me/theorems/274fe872-5e37-46e9-aa9a-26daae7663b7
-- title:
--   The undirected multicast Shapley network design game
-- statement:
--   Given a finite undirected graph $G$, edge costs $c_e$, a sink $t$ and sources $(s_i)_{i\in\iota}$, the **multicast Shapley game** is the congestion game in which player $i$ chooses a simple $s_i$–$t$ path $P_i$ and, if $k$ players use edge $e$, each of them pays $c_e/k$ for it. With the load $x_e(P)=|\{i : e\in P_i\}|$, player $i$'s payment is
--
--   $$
--   C_i(P)=\sum_{e\in P_i}\frac{c_e}{x_e(P)},
--   $$
--
--   and the Rosenthal potential of the game is $\Phi(P)=\sum_{e\in E} c_e H_{x_e(P)}$, where $H_0=0$ and $H_k=\sum_{j=1}^k 1/j$.
--
--   This is the game whose cheapest Nash equilibrium the mission compares with the social optimum.
--
--   **Formalization Note** The game is the published fair cost-sharing game `PriceOfStability.Harmonic.fairGame` with the strategy family `pathStrategies` and constant edge costs. Its `cost`, `potential` and `IsPureNash` are the payment, the potential (1) and the Nash condition of the paper. The cost function is defined on all of `Sym2 V`; only its values on edges of $G$ ever enter.
-- source:
--   Huang–Yuan, An O(log log n) Upper Bound on the Price of Stability for Undirected Multicast Shapley Games, STOC 2027 submission (manuscript sha256 dd0e08d0…), Section 1, p.1; Eq. (1), p.2; Section 2, p.4

import Mathlib
import Definitions.Def_PriceOfStability_Harmonic_Model
import Definitions.Def_MulticastPoS_pathStrategies

open CongestionPoA.AsymSum PriceOfStability.Harmonic

namespace MulticastPoS

/-- The undirected multicast Shapley network design game (Huang–Yuan, *An O(log log n) Upper
Bound on the Price of Stability for Undirected Multicast Shapley Games*, STOC 2027 submission
manuscript (sha256 dd0e08d0…f6d4), Section 1, p.1): players `ι` with sources `s i` and common
sink `t` in the graph `G` with edge costs `c`; player `i`'s strategies are the simple
`s i`–`t` paths (`pathStrategies`), and if `k` players use edge `e`, each pays `c e / k`.

**Formalization Note** This is the published fair cost-sharing congestion game
`PriceOfStability.Harmonic.fairGame` with constant edge costs `fun e _ => c e`, on the facility
type `Sym2 V`. Its `cost` is the payment `Cᵢ(P) = Σ_{e∈Pᵢ} c_e / x_e(P)` (p.4), its `potential`
is `Φ(P) = Σ_e c_e H_{x_e(P)}` (Eq. (1), p.2), and its `IsPureNash` is the Nash condition of
p.4. The costs `c` are a function on all of `Sym2 V`; every statement assumes nonnegativity on
`G.edgeSet` only, and `c` off the graph never enters (no strategy contains such an edge). -/
noncomputable def game {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph V) (c : Sym2 V → ℝ) (t : V) (s : ι → V) : CongestionGame ι (Sym2 V) :=
  fairGame (pathStrategies G t s) (fun e _ => c e)

end MulticastPoS


