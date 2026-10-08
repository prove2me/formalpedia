-- Prove2me | Definitions.Def_PriceOfStability_Undirected_Model
-- name    : PriceOfStability_Undirected_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T00:52:22.127201+00:00
-- url     : https://prove2.me/theorems/03e8efa1-c83a-497c-8d9a-3db408a115ee
-- title:
--   Sect. 2 and 4 — the two-player undirected fair connection game with a common terminal
-- statement:
--   This file sets up the game of Section 4 of Anshelevich et al. on top of the congestion-game layer `CongestionPoA.AsymSum.Model` (congestion games, loads $x_e$, player costs, profiles and pure Nash equilibria).
--
--   1. **Fair (Shapley) cost sharing.** Given strategy families $\Sigma_i$ and edge-cost functions $c_e(x)$, the fair game is the congestion game in which each of the $x_e$ users of edge $e$ pays $c_e(x_e)/x_e$. A player's cost is $C_i(S)=\sum_{e\in S_i} c_e(x_e)/x_e$.
--   2. **Total cost.** For a profile $S=(S_1,\dots,S_k)$, $$\mathrm{cost}(S)=\sum_{e\in \bigcup_i S_i} c_e(x_e),$$ the cost of the edges used by at least one player. For a set $F$ of edges and fixed costs $c_e$, $\mathrm{cost}(F)=\sum_{e\in F}c_e$.
--   3. **Undirected two-player game.** Let $G=(V,E)$ be a finite undirected simple graph with fixed edge costs $c_e$, a common terminal $s$ and personal terminals $t_1,t_2$. A strategy of player $i$ is a set of edges $S_i\subseteq E$ that connects $t_i$ with $s$, i.e. $t_i$ and $s$ lie in the same connected component of the graph $(V,S_i)$. The game is the fair game with these strategy families and constant cost functions $c_e(x)=c_e$.
--   4. **Minimal strategies.** A strategy $T$ of player $i$ is inclusion-minimal if no proper subset of $T$ connects $t_i$ with $s$; such a set is a simple $t_i$–$s$ path (or empty when $t_i=s$).
--
--   These objects are shared by every statement of the mission: Claim 4.1, inequalities (4.1) and (4.2), and the deviation inequalities of its proof.
--
--   **Formalization Note.** Edges are unordered pairs (`Sym2 V`). Strategies are arbitrary connecting edge sets of $G$, not only paths, as in the paper's model. Players $1,2$ of the paper are `0`, `1` of `Fin 2`. Lean's $c/0=0$ at load $0$ is never used. Inclusion-minimality is not a notion of the paper's model; it states the implicit assumption of the proof of Claim 4.1 that the reference solution consists of paths.
-- source:
--   Anshelevich et al., The Price of Stability for Network Design with Fair Cost Allocation, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096, p. 1607 (PDF p. 6), Sect. 2; p. 1613 (PDF p. 12), Sect. 4 and Claim 4.1, proof

import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_PriceOfStability_Harmonic_Model
open CongestionPoA.AsymSum

namespace PriceOfStability.Undirected

section General

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

/-- `cost(F) = Σ_{e ∈ F} c_e` (Claim 4.1, proof, p. 1613, PDF p. 12): the cost of a set of edges
under fixed edge costs. -/
def setCost (c : E → ℝ) (F : Finset E) : ℝ := ∑ e ∈ F, c e

end General

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- Player `i`'s strategies in the undirected fair connection game with a common terminal `s`
(Sect. 2, p. 1607, PDF p. 6, specialised by Sect. 4, p. 1613, PDF p. 12): "a set of edges
`Sᵢ ⊂ E` such that `Sᵢ` connects all nodes in `Tᵢ`", with `Tᵢ = {tᵢ, s}`. Formally, the edge sets
`S ⊆ E(G)` such that `tᵢ` and `s` lie in the same connected component of the graph `(V, S)`.

**Formalization Note.** Edges are unordered pairs `Sym2 V`; strategies are arbitrary connecting edge
sets (not only paths), as in the paper's model. If `tᵢ = s`, the empty set is a strategy. -/
noncomputable def connStrategies (G : SimpleGraph V) (s : V) {ι : Type*} (t : ι → V) (i : ι) :
    Finset (Finset (Sym2 V)) :=
  (Finset.univ : Finset (Sym2 V)).powerset.filter (fun S =>
    (S : Set (Sym2 V)) ⊆ G.edgeSet ∧
      (SimpleGraph.fromEdgeSet (S : Set (Sym2 V))).Reachable (t i) s)

/-- The two-player undirected fair connection game of Sect. 4 (p. 1613, PDF p. 12): graph `G`,
fixed edge costs `c`, common terminal `s`, personal terminals `t 0`, `t 1` (the paper's `t₁`, `t₂`),
with Shapley cost sharing. -/
noncomputable def twoPlayerGame (G : SimpleGraph V) (c : Sym2 V → ℝ) (s : V) (t : Fin 2 → V) :
    CongestionGame (Fin 2) (Sym2 V) :=
  PriceOfStability.Harmonic.fairGame (connStrategies G s t) (fun e _ => c e)

/-- An inclusion-minimal strategy of player `i`: a connecting edge set `T` none of whose proper
subsets connects `tᵢ` with `s` (in a graph, a simple `tᵢ`–`s` path, or `∅` when `tᵢ = s`).

**Formalization Note.** The proof of Claim 4.1 (p. 1613, PDF p. 12) treats the strategies of the
reference solution as paths ("following X₁ until X₁ meets with X₂"); this predicate is how that
implicit assumption is stated. -/
def IsMinimalStrategy (G : SimpleGraph V) (s : V) {ι : Type*} (t : ι → V) (i : ι)
    (T : Finset (Sym2 V)) : Prop :=
  T ∈ connStrategies G s t i ∧ ∀ T' ⊂ T, T' ∉ connStrategies G s t i

end Graph

end PriceOfStability.Undirected


