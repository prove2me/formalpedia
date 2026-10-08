-- Prove2me | Definitions.Def_WorstCaseEq_Speeds_Model
-- name    : WorstCaseEq_Speeds_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:09:56.781345+00:00
-- url     : https://prove2.me/theorems/de0a8b5c-f947-4326-8199-02ebc0e71fb9
-- title:
--   The model, PDF pp. 2–6 — load balancing on links with speeds: delays, Nash equilibrium, M^j, c_i^j of (8), social cost (4), opt, and the instance of Theorem 4
-- statement:
--   **Agents and links.** There are $n$ agents and $m$ parallel links. Agent $i$ has an amount of traffic $w_i$ to send, and link $j$ has a speed $s_j$. A **pure profile** $a=(a_1,\dots,a_n)\in\{1,\dots,m\}^n$ assigns each agent to one link. The **load** of link $j$ under $a$ is the total traffic on it,
--   $$
--   L_j(a)=\sum_{k\,:\,a_k=j} w_k,
--   $$
--   and an agent on link $j$ experiences the **delay** $L_j(a)/s_j$.
--
--   **Mixed strategies and equilibria.** A mixed strategy of agent $i$ is a probability distribution $(p_i^1,\dots,p_i^m)$ on the links, where $p_i^j$ is the probability that agent $i$ chooses link $j$; the agents randomize independently. The **expected cost** $c_i$ of agent $i$ is its expected delay over the product distribution. A profile $p$ is a **Nash equilibrium** if every $p_i$ is a probability distribution and no agent can lower its expected cost by switching unilaterally to any other distribution.
--
--   **Expected traffic and link costs.** The expected traffic on link $j$ is $M^j=\sum_i p_i^j w_i$ ((1), PDF p. 3), and the cost to agent $i$ of placing its traffic on link $j$, the others keeping their strategies, is
--   $$
--   c_i^j=\frac{w_i+\sum_{k\neq i}p_k^j w_k}{s_j}\qquad\text{((2), PDF p. 3, divided by the speed as in (8), PDF p. 6).}
--   $$
--
--   **Social cost and optimum.** The **makespan** of a pure profile is the largest delay over the links, $\max_j L_j(a)/s_j$. The **social cost** of a mixed profile is the expected makespan over the product distribution,
--   $$
--   \operatorname{cost}(p)=\sum_{a}\Big(\prod_i p_i^{a_i}\Big)\max_j \frac{L_j(a)}{s_j},
--   $$
--   ((4), PDF p. 4, with each load divided by its link's speed), and $\operatorname{opt}$ is the least makespan over all pure assignments.
--
--   **The instance of Theorem 4** (PDF p. 6). Two links with speeds $(s_1,s_2)$, two agents with traffic $w_1=s_2$ and $w_2=s_1$, and the mixed profile
--   $$
--   p_1^1=\frac{s_1^2}{s_2(s_1+s_2)},\qquad p_2^1=1-\frac{s_2^2}{s_1(s_1+s_2)},\qquad p_i^2=1-p_i^1 .
--   $$
--
--   These are the objects of the price-of-anarchy question for parallel links with different capacities: how much larger the social cost of a Nash equilibrium can be than the optimum.
--
--   **Formalization Note** The game is built on the published `agt_games` vocabulary (`AGT.IsMixedNash`, `AGT.expectedPayoff`, `AGT.profileProb`), which maximizes payoffs, so the payoff of an agent is minus its delay and the expected cost is minus the expected payoff. Agents and links are `Fin n` and `Fin m`, indexed from $0$: the paper's link 1, 2 and agent 1, 2 are `0, 1`. A mixed profile is a function `p : Fin n → Fin m → ℝ`; being a family of probability distributions is part of the Nash condition, not of the type. The paper does not print the social cost for links with speeds; the cost computation in the proof of Theorem 4 (PDF p. 6) is the expected maximum over links of load divided by speed, and that is the definition used here. The makespan, social cost and optimum require at least one link (`NeZero m`), which the paper assumes implicitly. Positivity of the traffic and of the speeds is not built into the definitions; the theorems state it where it is needed.
-- source:
--   Koutsoupias & Papadimitriou, Worst-case equilibria (journal version, 2009), PDF p. 2 (The model), PDF p. 3 ((1), (2)), PDF p. 4 ((4)), PDF p. 6 (Links with different capacities, (8); proof of Theorem 4)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WorstCaseEq_Identical_Model

noncomputable section

namespace WorstCaseEq.Speeds

/-!
Load balancing on `m` parallel links with speeds (Koutsoupias & Papadimitriou, *Worst-case
equilibria*, journal version 2009: *The model*, PDF p. 2; §2, PDF p. 3; (4), PDF p. 4;
§3 *Links with different capacities*, (8), PDF p. 6).

Agents `Fin n` with traffic `w i`, links `Fin m` with speeds `s j`.  A pure profile
`a : Fin n → Fin m` sends agent `i` to link `a i`; an agent on link `j` carrying total traffic `L`
experiences delay `L / s j`.  A mixed profile `p : Fin n → Fin m → ℝ` gives `p i j = p_i^j`, the
probability that agent `i` picks link `j`.  The game is cast in the payoff-maximizing convention of
`agt_games`: the payoff is minus the delay.
-/

variable {n m : ℕ}

/-- The payoff of agent `i` under the pure profile `a`: minus its delay `load w a (a i) / s (a i)`,
the traffic on its link divided by the link's speed (*The model*, PDF p. 2, with speeds as in §3,
PDF p. 6). -/
def payoff (w : Fin n → ℝ) (s : Fin m → ℝ) : Fin n → (Fin n → Fin m) → ℝ :=
  fun i a => -(WorstCaseEq.Identical.load w a (a i) / s (a i))

/-- `p` is a (mixed) Nash equilibrium of the game with traffic `w` and speeds `s`: a profile of
lotteries from which no agent can lower its expected delay by switching to any other lottery. -/
def IsNash (w : Fin n → ℝ) (s : Fin m → ℝ) (p : Fin n → Fin m → ℝ) : Prop :=
  AGT.IsMixedNash (payoff w s) p

/-- The expected cost (expected delay) `c_i` of agent `i` under the mixed profile `p`. -/
def expCost (w : Fin n → ℝ) (s : Fin m → ℝ) (p : Fin n → Fin m → ℝ) (i : Fin n) : ℝ :=
  -AGT.expectedPayoff (payoff w s) p i

/-- The cost `c_i^j = (w_i + ∑_{k ≠ i} p_k^j w_k) / s_j` to agent `i` of assigning its traffic to
link `j` ((2), PDF p. 3, divided by the speed as in (8), PDF p. 6). -/
def linkCost (w : Fin n → ℝ) (s : Fin m → ℝ) (p : Fin n → Fin m → ℝ) (i : Fin n) (j : Fin m) : ℝ :=
  (w i + ∑ k ∈ Finset.univ.erase i, p k j * w k) / s j

section NeZero

variable [NeZero m]

/-- The makespan of the pure profile `a`: the largest delay `load w a j / s j` over the links. -/
def makespan (w : Fin n → ℝ) (s : Fin m → ℝ) (a : Fin n → Fin m) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => WorstCaseEq.Identical.load w a j / s j)

/-- The social cost of the mixed profile `p` ((4), PDF p. 4, with speeds): the expected makespan
over the product distribution, `∑_a (∏_i p_i^{a_i}) · max_j load_j(a) / s_j`. -/
def socialCost (w : Fin n → ℝ) (s : Fin m → ℝ) (p : Fin n → Fin m → ℝ) : ℝ :=
  ∑ a : Fin n → Fin m, AGT.profileProb p a * makespan w s a

/-- The optimum `opt`: the least makespan over all pure assignments of the agents to the links. -/
def opt (w : Fin n → ℝ) (s : Fin m → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (makespan w s)

end NeZero

/-- The speeds `(s₁, s₂)` of the two links of Theorem 4 (links 1, 2 of the paper are `0, 1`). -/
def speeds (s₁ s₂ : ℝ) : Fin 2 → ℝ := ![s₁, s₂]

/-- The traffic of the two agents in the proof of Theorem 4, PDF p. 6: `w₁ = s₂`, `w₂ = s₁`
(agents 1, 2 of the paper are `0, 1`). -/
def instWeights (s₁ s₂ : ℝ) : Fin 2 → ℝ := ![s₂, s₁]

/-- The mixed profile in the proof of Theorem 4, PDF p. 6 (row = agent, column = link):
`p₁¹ = s₁²/(s₂(s₁+s₂))`, `p₂¹ = 1 − s₂²/(s₁(s₁+s₂))`, and `p_i² = 1 − p_i¹`. -/
def instProfile (s₁ s₂ : ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![s₁ ^ 2 / (s₂ * (s₁ + s₂)), 1 - s₁ ^ 2 / (s₂ * (s₁ + s₂))],
    ![1 - s₂ ^ 2 / (s₁ * (s₁ + s₂)), s₂ ^ 2 / (s₁ * (s₁ + s₂))]]

end WorstCaseEq.Speeds

end


