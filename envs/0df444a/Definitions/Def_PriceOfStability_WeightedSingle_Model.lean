-- Prove2me | Definitions.Def_PriceOfStability_WeightedSingle_Model
-- name    : PriceOfStability_WeightedSingle_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T20:00:54.895457+00:00
-- url     : https://prove2.me/theorems/5fd6d03d-d5bb-4645-9812-84ffadc2346e
-- title:
--   Sect. 6 — the weighted cost-sharing game: weights, edge weights $W_e$, payments $\tfrac{w_i}{W_e}c_e$ and pure Nash equilibria
-- statement:
--   This file sets up the **weighted cost-sharing game** of Section 6 of Anshelevich et al.
--
--   Let $\iota$ be a finite set of players and $E$ a finite ground set of edges (resources). A weighted game consists of
--
--   1. for each player $i$, a finite family $\Sigma_i$ of **feasible strategies**, each a subset of $E$;
--   2. a **weight** $w_i$ for each player $i$;
--   3. a fixed **cost** $c_e$ for each edge $e$.
--
--   The **standing assumptions** are $w_i \ge 1$ for every player (Section 6) and $c_e \ge 0$ for every edge (Section 2).
--
--   A **profile** is a choice $S=(S_i)_{i\in\iota}$ with $S_i\in\Sigma_i$ for every $i$. For a profile $S$ and an edge $e$, let $W_e$ be the total weight of the players using $e$,
--   $$W_e=\sum_{i\,:\,e\in S_i} w_i ,$$
--   and let player $i$ pay, for each edge it uses, the share of the edge's cost proportional to its weight:
--   $$\mathrm{pay}_i(S)=\sum_{e\in S_i}\frac{w_i}{W_e}\,c_e .$$
--
--   A profile $S$ is a **(pure) Nash equilibrium** if no player can lower its payment by a unilateral switch: for every player $i$ and every $T\in\Sigma_i$, $\mathrm{pay}_i(S)\le \mathrm{pay}_i(S_{-i},T)$.
--
--   These objects are shared by every statement of the mission. With all weights equal the payment is the fair (Shapley) share $c_e/x_e$ of Sections 1–5.
--
--   **Formalization Note.** Strategies are finite subsets of a finite ground set; the network games of Theorem 6.3 are the instance in which $\Sigma_i$ is the set of arc sets of simple $s$–$t$ paths (next definition item). The standing assumptions are the predicate `IsStandard`, not built into the structure. Lean's real division $x/0=0$ is never reached in a payment: on every edge of $S_i$, $W_e\ge w_i$.
-- source:
--   Anshelevich et al., The Price of Stability for Network Design with Fair Cost Allocation, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096, p. 1619 (PDF p. 18), Sect. 6; p. 1607 (PDF p. 6), Sect. 2; Nash equilibrium p. 1604 (PDF p. 3)

import Mathlib

/-!
# The weighted cost-sharing game of Sect. 6

Anshelevich, Dasgupta, Kleinberg, Tardos, Wexler and Roughgarden, *The Price of Stability for
Network Design with Fair Cost Allocation*, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096,
Sect. 6, p. 1619 (PDF p. 18), with the model of Sect. 2, p. 1607 (PDF p. 6).

**Formalization Note.** A strategy is a finite set of edges (resources) of a finite ground set `E`,
and each player `i` has a finite family `G.strategies i` of feasible strategies. The network
games of Theorem 6.3 are the instance in which every family is the set of arc sets of simple
`s`–`t` paths (`Def_PriceOfStability_WeightedSingle_SingleCommodity`).
-/

namespace PriceOfStability.WeightedSingle

/-- Sect. 6 (p. 1619): a weighted cost-sharing game on players `ι` and edges/resources `E`:
feasible strategies `Σᵢ` (each a set of edges), player weights `wᵢ` and fixed edge costs `c_e`. -/
structure WeightedGame (ι : Type*) (E : Type*) where
  /-- the feasible strategies of player `i`, each a set of edges -/
  strategies : ι → Finset (Finset E)
  /-- `wᵢ` -/
  weight : ι → ℝ
  /-- `c_e` (fixed edge cost) -/
  edgeCost : E → ℝ

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

/-- Standing assumptions of Sect. 6 and Sect. 2: weights `wᵢ ≥ 1` (p. 1619) and nonnegative edge
costs `c_e ≥ 0` (p. 1607). -/
def WeightedGame.IsStandard (G : WeightedGame ι E) : Prop :=
  (∀ i, 1 ≤ G.weight i) ∧ ∀ e, 0 ≤ G.edgeCost e

/-- `W_e`: the total weight of the players using `e` in the profile `S` (p. 1619). -/
def edgeWeight (G : WeightedGame ι E) (S : ι → Finset E) (e : E) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => e ∈ S i), G.weight i

/-- Player `i`'s payment `Σ_{e∈Sᵢ} (wᵢ/W_e) c_e` (p. 1619). On every edge `e ∈ Sᵢ` the
denominator satisfies `W_e ≥ wᵢ`, so it is positive whenever the weights are. -/
noncomputable def payment (G : WeightedGame ι E) (S : ι → Finset E) (i : ι) : ℝ :=
  ∑ e ∈ S i, G.weight i / edgeWeight G S e * G.edgeCost e

/-- `S` is a strategy profile: every player plays a feasible strategy. -/
def IsProfile (G : WeightedGame ι E) (S : ι → Finset E) : Prop := ∀ i, S i ∈ G.strategies i

/-- Pure Nash equilibrium (cost form, as on p. 1604): `S` is a profile and no player can lower
its payment by a unilateral switch to another feasible strategy. -/
def IsNash (G : WeightedGame ι E) (S : ι → Finset E) : Prop :=
  IsProfile G S ∧ ∀ i, ∀ T ∈ G.strategies i, payment G S i ≤ payment G (Function.update S i T) i

end PriceOfStability.WeightedSingle


