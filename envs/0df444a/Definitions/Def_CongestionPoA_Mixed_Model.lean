-- Prove2me | Definitions.Def_CongestionPoA_Mixed_Model
-- name    : CongestionPoA_Mixed_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:50:34.223346+00:00
-- url     : https://prove2.me/theorems/84e64fc6-e9e8-49c0-92e1-af716aef0254
-- title:
--   Sect. 2 and 5 — congestion games, loads, costs, linear latencies, mixed Nash equilibria, expected costs and loads, the mixed social cost
-- statement:
--   This bundle sets up the congestion games of Christodoulou and Koutsoupias (Sect. 2), together with their mixed strategies and the mixed social cost of Sect. 5.
--
--   1. **Congestion game.** A finite set $N$ of players and a finite set $E$ of facilities. Each player $i$ has a collection $\Sigma_i \subseteq 2^E$ of pure strategies, each a set of facilities, and each facility $e$ has a latency function $f_e : \mathbb N \to \mathbb R$ of its number of users.
--   2. **Loads and costs.** For a pure profile $A = (A_1,\dots,A_n)$ with $A_i \subseteq E$, the load $n_e(A)$ is the number of players $i$ with $e \in A_i$, and the cost of player $i$ is
--   $$c_i(A) = \sum_{e \in A_i} f_e\bigl(n_e(A)\bigr).$$
--   $A$ is a pure strategy profile when $A_i \in \Sigma_i$ for every $i$, and its social cost is $\mathrm{SUM}(A) = \sum_{i \in N} c_i(A)$.
--   3. **Linear latencies.** The game is linear when $f_e(k) = a_e k + b_e$ for nonnegative constants $a_e, b_e$.
--   4. **Mixed strategies.** A mixed strategy $p_i$ of player $i$ is a probability distribution on $\Sigma_i$; the players randomize independently, so the pure profile $s$ is drawn with probability $\Pr(s) = \prod_j p_j(s_j)$. The expected cost of player $i$ is $\mathbb E[c_i] = \sum_s \Pr(s)\, c_i(s)$ and the expected load of facility $e$ is $\mathbb E[n_e] = \sum_s \Pr(s)\, n_e(s)$.
--   5. **Mixed Nash equilibrium.** A mixed profile $p$ is a mixed Nash equilibrium if no player can lower their expected cost by switching unilaterally to another probability distribution on $\Sigma_i$.
--   6. **Mixed social cost.** The social cost of a mixed profile is the sum of the players' expected costs,
--   $$\mathrm{SUM}(p) = \sum_{i \in N} \mathbb E[c_i].$$
--
--   These are the objects of the paper's mixed price of anarchy bound (Theorem 14) and of the steps of Theorem 1's proof that carry over to mixed equilibria.
--
--   **Formalization Note** Mixed strategies, independent randomization and mixed Nash equilibria are taken from the platform definition `agt_games` (`AGT.IsLottery`, `AGT.profileProb`, `AGT.IsMixedNash`), with player $i$'s strategy type the finite set $\Sigma_i$ and payoff $-c_i$: `agt_games` maximizes payoffs, the paper minimizes costs. Deviations range over all distributions on $\Sigma_i$, which is equivalent to deviations to pure strategies. Profiles of facility sets are functions to `Finset E`, with feasibility a separate predicate. The printed "$(f_e)_{e\in M}$" and "facility $j$" of Sect. 2 are read as $e \in E$, facility $e$; the printed "$c_i(N)$" of Sect. 5 is read as the expected cost of player $i$. The second social cost of Sect. 5, $\sum_e \mathbb E[n_e^2]$, is not defined here.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 2, Sect. 2 (The Model, incl. mixed strategies); PDF p. 6, Sect. 5 (mixed social cost)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_CongestionPoA_AsymSum_Model

namespace CongestionPoA.Mixed

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

/-- The payoff function of the congestion game `G` as a game in the sense of `agt_games`
(Sect. 2, PDF p. 2): player `i`'s pure strategies are the elements of `Σᵢ` (the finite type
`↥(G.strategies i)`), and on the pure profile `s` player `i` receives `−cᵢ(s)`, the negative of their
cost on the profile of facility sets `j ↦ s_j`.

**Formalization Note.** `agt_games` is payoff-maximizing; the paper's players minimize cost. The sign
flip makes the two conventions agree. -/
noncomputable def payoff (G : CongestionPoA.AsymSum.CongestionGame ι E) :
    ι → (∀ i, ↥(G.strategies i)) → ℝ :=
  fun i s => -CongestionPoA.AsymSum.cost G (fun j => (s j).1) i

/-- Mixed Nash equilibrium of a congestion game (Sect. 2, PDF p. 2: "A *mixed* strategy pᵢ for a
player i, is a probability distribution over his pure strategy set Σᵢ. The above definitions extend
naturally to this case (with expected costs, of course)"): `σ` assigns to each player `i` a probability
distribution `σ i` on `Σᵢ`, the players randomize independently, and no player can lower their
expected cost by switching unilaterally to another probability distribution on `Σᵢ`.

**Formalization Note.** This is `AGT.IsMixedNash` of `agt_games` applied to `payoff G`; lowering the
expected cost is raising the expected payoff `−cost`. Deviations range over all lotteries, which is
equivalent to deviations to pure strategies (a point mass is a lottery, and an expected payoff is
linear in the deviating player's lottery). -/
def IsMixedNash (G : CongestionPoA.AsymSum.CongestionGame ι E) (σ : ∀ i, ↥(G.strategies i) → ℝ) : Prop :=
  AGT.IsMixedNash (payoff G) σ

/-- The expected cost `E[cᵢ]` of player `i` under the mixed profile `σ` (Sect. 2, PDF p. 2, "with
expected costs"; Sect. 5, PDF p. 6): the expectation of `cᵢ(s)` when the pure profile `s` is drawn
from the product distribution `Prob(s) = Πⱼ σⱼ(sⱼ)`.

**Formalization Note.** This is the expected value of the cost, not the cost of an averaged profile;
it equals `−AGT.expectedPayoff (payoff G) σ i`. -/
noncomputable def expCost (G : CongestionPoA.AsymSum.CongestionGame ι E) (σ : ∀ i, ↥(G.strategies i) → ℝ) (i : ι) : ℝ :=
  ∑ s : ∀ j, ↥(G.strategies j), AGT.profileProb σ s * CongestionPoA.AsymSum.cost G (fun j => (s j).1) i

/-- The expected load `E[n_e]` of facility `e` under the mixed profile `σ`: the expected number of
players using `e` when the pure profile is drawn from `Prob(s) = Πⱼ σⱼ(sⱼ)`. -/
noncomputable def expLoad (G : CongestionPoA.AsymSum.CongestionGame ι E) (σ : ∀ i, ↥(G.strategies i) → ℝ) (e : E) : ℝ :=
  ∑ s : ∀ j, ↥(G.strategies j), AGT.profileProb σ s * (CongestionPoA.AsymSum.load (fun j => (s j).1) e : ℝ)

/-- The social cost of a mixed profile (Sect. 5, PDF p. 6): "the average (or sum) of the expected cost
of all players SUM = Σ_{i∈N} cᵢ(N)", i.e. `Σᵢ E[cᵢ]`.

**Formalization Note.** The printed argument "`cᵢ(N)`" stands for the expected cost of player `i`
under the mixed profile. The paper's second option, `Σ_e E[n_e²]`, is not this definition. -/
noncomputable def mixedSumCost (G : CongestionPoA.AsymSum.CongestionGame ι E) (σ : ∀ i, ↥(G.strategies i) → ℝ) : ℝ :=
  ∑ i, expCost G σ i

end CongestionPoA.Mixed


