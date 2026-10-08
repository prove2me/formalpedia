-- Prove2me | Definitions.Def_PriceOfStability_WeightedPotential_Model
-- name    : PriceOfStability_WeightedPotential_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:10:59.778437+00:00
-- url     : https://prove2.me/theorems/d4de2ed1-e99c-41b4-afa7-370153f54fa5
-- title:
--   Sect. 6 — the weighted cost-sharing game, its Nash equilibria, strategy spaces and the potential $\Phi$ of Theorem 6.1
-- statement:
--   A **weighted cost-sharing game** consists of a finite set of players, a finite ground set $E$ of edges (resources), for each player $i$ a finite family $\Sigma_i$ of feasible strategies (each a subset of $E$), a weight $w_i$ for each player and a fixed cost $c_e$ for each edge. The game is **standard** when $w_i \ge 1$ for every player and $c_e \ge 0$ for every edge, the standing assumptions of the paper's Sect. 6 and Sect. 2.
--
--   A **profile** $S = (S_i)_i$ assigns each player a feasible strategy $S_i \in \Sigma_i$. For an edge $e$ let $W_e$ be the total weight of the players using $e$ in $S$. Player $i$ pays a share of each edge it uses proportional to its weight:
--
--   $$
--   C_i(S) = \sum_{e \in S_i} \frac{w_i}{W_e}\, c_e .
--   $$
--
--   A profile is a **(pure) Nash equilibrium** when no player can lower its payment by switching unilaterally to another feasible strategy.
--
--   The **strategy space** of player $i$ is the set of edges that occur in at least one strategy in $\Sigma_i$.
--
--   The **potential** of Theorem 6.1 is $\Phi(S) = \sum_{e} \Phi_e(S)$, where $\Phi_e(S)$ depends on who uses $e$ in $S$: it is $0$ if nobody uses $e$, $c_e w_i$ if exactly one player $i$ uses $e$, and $c_e\theta_{ij}$ if exactly two players $i, j$ use $e$, with
--
--   $$
--   \theta_{ij} = w_i + w_j - \frac{w_i w_j}{w_i + w_j}.
--   $$
--
--   These are the objects of Sect. 6: a game with weight-proportional cost sharing, which generalizes the fair (Shapley) sharing of the rest of the paper, and the potential function used to show that equilibria exist when each edge serves at most two players.
--
--   **Formalization Note** Strategies are arbitrary subsets of a finite ground set, as the remark after Theorem 6.1 allows; the network design game is the instance in which $\Sigma_i$ is the set of edge sets of $s_i$–$t_i$ paths. $\Phi_e$ is read off the set of current users of $e$; under the hypothesis of Theorem 6.1 (each edge in at most two strategy spaces) this agrees with the paper's case display. The value $0$ for three or more users is a placeholder that never arises under that hypothesis.
-- source:
--   Anshelevich et al., The Price of Stability for Network Design with Fair Cost Allocation, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096, p. 1619 (PDF p. 18), Sect. 6, and Theorem 6.1, proof, pp. 1619–1620 (PDF pp. 18–19), definition of Φ_e, θ_ij and Φ

import Mathlib

/-!
# The weighted cost-sharing game of Sect. 6 and the potential of Theorem 6.1

Anshelevich, Dasgupta, Kleinberg, Tardos, Wexler and Roughgarden, *The Price of Stability for
Network Design with Fair Cost Allocation*, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096,
Sect. 6, p. 1619 (PDF p. 18), and the proof of Theorem 6.1, pp. 1619–1620 (PDF pp. 18–19).

**Formalization Note.** Following the remark after the proof of Theorem 6.1 (p. 1620: the theorem
holds "also for the generalized model in which players select subsets from some ground set"), a
strategy is an arbitrary finite subset of a finite ground set `E` of edges (resources), and each
player `i` has a finite family `G.strategies i` of feasible strategies. The network design game is
the instance in which `G.strategies i` is the set of edge sets of `sᵢ`–`tᵢ` paths.
-/

namespace PriceOfStability.WeightedPotential

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

/-- The strategy space of player `i` (Theorem 6.1, p. 1619): the edges that occur in at least one
feasible strategy of `i`. Theorem 6.1 assumes each edge lies in the strategy spaces of at most two
players. -/
def strategySpace (G : WeightedGame ι E) (i : ι) : Finset E :=
  (G.strategies i).biUnion id

/-- The players using edge `e` in the profile `S`. -/
def users (S : ι → Finset E) (e : E) : Finset ι :=
  Finset.univ.filter (fun i => e ∈ S i)

/-- The edge potential `Φ_e(S)` of the proof of Theorem 6.1 (pp. 1619–1620):

"For each edge e used by players i and j, define Φ_e(S) = c_e w_i if player i uses e in S;
c_e w_j if player j uses e in S; c_e θ_ij if both players i and j use e in S; 0 otherwise,
where θ_ij = (w_i + w_j − w_i w_j/(w_i+w_j)). For any edge e with only one player i, simply set
Φ_e(S) = w_i c_e if i uses e and 0 otherwise."

**Formalization Note.** The value is read off the set of players that actually use `e` in `S`:
one user `i` gives `c_e wᵢ` (here `W_e = wᵢ`), two users `i, j` give `c_e θᵢⱼ`, written as
`c_e (W_e − wᵢwⱼ/W_e)` with `W_e = wᵢ + wⱼ`, and no user gives `0`. When each edge lies in the
strategy spaces of at most two players (the hypothesis of Theorem 6.1), the users of `e` in any
profile are among those two players, so this is exactly the paper's case display. Three or more
users never occur under that hypothesis; the value `0` assigned to that case is a placeholder
the theorem never sees. -/
noncomputable def edgePotential (G : WeightedGame ι E) (S : ι → Finset E) (e : E) : ℝ :=
  if (users S e).card = 1 then G.edgeCost e * edgeWeight G S e
  else if (users S e).card = 2 then
    G.edgeCost e * (edgeWeight G S e - (∏ i ∈ users S e, G.weight i) / edgeWeight G S e)
  else 0

/-- The potential `Φ(S) = Σ_e Φ_e(S)` of the proof of Theorem 6.1 (p. 1620). -/
noncomputable def potential (G : WeightedGame ι E) (S : ι → Finset E) : ℝ :=
  ∑ e, edgePotential G S e

end PriceOfStability.WeightedPotential


