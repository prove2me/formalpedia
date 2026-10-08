-- Prove2me | Definitions.Def_WorstCaseEq_Identical_Model
-- name    : WorstCaseEq_Identical_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:16:23.94696+00:00
-- url     : https://prove2.me/theorems/c9f3187d-6cb0-4083-8b45-6c141c114b67
-- title:
--   The model, PDF pp. 2–5 — load balancing on m identical links: payoff, Nash equilibrium, (1), (2), social cost (4), opt, t_ik, q_i
-- statement:
--   This module sets up the game of Koutsoupias and Papadimitriou on $m$ identical parallel links.
--
--   There are $n$ agents; agent $i$ has an amount of traffic $w_i$ to send over one of $m$ parallel links. A **pure profile** assigns each agent a link, $s=(j_1,\dots,j_n)\in\{1,\dots,m\}^n$. The **load** of link $j$ under $s$ is the total traffic routed over it, and the cost of agent $i$ is the load of its own link:
--   $$
--   \ell_j(s)=\sum_{k:\,j_k=j} w_k,\qquad c_i(s)=\ell_{j_i}(s).
--   $$
--   A **mixed strategy** of agent $i$ is a probability distribution $(p_i^1,\dots,p_i^m)$ on the links, and the agents randomize independently, so the pure profile $s$ occurs with probability $\prod_i p_i^{j_i}$. The module defines:
--
--   1. **Nash equilibrium.** The profile $p$ is a Nash equilibrium if every $p_i$ is a probability distribution and no agent $i$ can lower its expected cost by switching unilaterally to any other distribution on the links.
--   2. **Expected cost** $c_i$ of agent $i$: the expectation of $c_i(s)$ under the product distribution.
--   3. **Expected traffic** on link $j$, (1): $M^j=\sum_i p_i^j w_i$.
--   4. **Link cost**, (2): the cost of agent $i$ when its own traffic is assigned to link $j$, $c_i^j=w_i+\sum_{k\neq i}p_k^j w_k$.
--   5. **Pure lottery** on link $j$: the distribution putting probability $1$ on $j$.
--   6. **Makespan** of a pure profile, $\max_j \ell_j(s)$, and the **social cost** (4), the expected maximum traffic over all links:
--   $$
--   \mathrm{cost}=\sum_{j_1=1}^m\cdots\sum_{j_n=1}^m\prod_{i=1}^n p_i^{j_i}\,\max_{j=1,\dots,m}\sum_{k:\,j_k=j}w_k .
--   $$
--   7. **Social optimum** $\mathrm{opt}$: the least makespan over all pure assignments of the $n$ agents to the $m$ links (the optimum of the $m$-way load balancing problem).
--   8. **Collision probability** $t_{ik}=\sum_j p_i^j p_k^j$ of agents $i$ and $k$.
--   9. **Contribution probability** $q_i$: the probability that agent $i$ is on the link of maximum load, where among several links of maximum load the lexicographically first (lowest-indexed) one is taken.
--
--   These are the objects of every result of §§2–3 of the paper: Theorem 2 bounds $c_i$, and Theorem 3 bounds the social cost by $\tfrac32\,\mathrm{opt}$ on two links through $q_i$ and $t_{ik}$.
--
--   **Formalization Note** Agents are `Fin n` and links `Fin m`, so the paper's agent $i$ and link $j$ are indices $i-1$ and $j-1$. A mixed profile is a function `p : Fin n → Fin m → ℝ` with `p i j` $=p_i^j$; it is a mixed profile of the published `agt_games` vocabulary with every agent's strategy set equal to the links. That vocabulary maximizes payoffs, so the payoff of agent $i$ is $-c_i(s)$ and the expected cost is minus the expected payoff; the Nash equilibrium is `AGT.IsMixedNash`, which includes that each $p_i$ is a probability distribution. The paper's equivalent description of equilibria through supports is a theorem of this mission, not the definition. The social cost is the expected **maximum** load, not the maximum of the expected loads $M^j$. The number of links $m$ is an explicit argument of `opt`, and makespan, social cost, opt and $q_i$ assume $m\ge 1$ (`NeZero m`), which the paper takes for granted. Decidability of the "first maximum link" test is classical.
-- source:
--   Koutsoupias & Papadimitriou, Worst-case equilibria (journal version, 2009), PDF pp. 2–5, The model (p. 2), (1), (2) (p. 3), (4) and opt (p. 4), contribution and collision probabilities (proof of Theorem 3, p. 5)

import Mathlib
import Definitions.Def_agt_games

namespace WorstCaseEq.Identical

/-!
The load-balancing game of Koutsoupias & Papadimitriou, *Worst-case equilibria* (journal version, 2009),
*The model* (PDF p. 2), §2 (PDF pp. 3–4) and the proof of Theorem 3 (PDF p. 5): `n` agents with traffic
`w i` each choose one of `m` identical parallel links. Agents are `Fin n`, links are `Fin m` (the paper's
agents and links are numbered from 1, here from 0). A mixed profile is `p : Fin n → Fin m → ℝ`, with
`p i j` the probability `p_i^j` that agent `i` picks link `j`. The game is encoded on top of the published
`agt_games` vocabulary, which maximizes payoffs, so the payoff of an agent is minus its cost.
-/

noncomputable section

variable {n m : ℕ}

/-- The traffic on link `j` under the pure profile `s` (agent `k` on link `s k`):
`∑_{k : j_k = j} w_k`. -/
def load (w : Fin n → ℝ) (s : Fin n → Fin m) (j : Fin m) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k => s k = j), w k

/-- The payoff of agent `i` in the pure profile `s`: minus its cost `c_i = ∑_{k : j_k = j_i} w_k`,
the traffic on the link agent `i` chose (PDF p. 2). -/
def payoff (w : Fin n → ℝ) : Fin n → (Fin n → Fin m) → ℝ :=
  fun i s => -load w s (s i)

/-- A (mixed) Nash equilibrium of the game: `p` is a profile of lotteries over the links from which no
agent can lower its expected cost by switching unilaterally to any other lottery (PDF pp. 2–3). -/
def IsNash (w : Fin n → ℝ) (p : Fin n → Fin m → ℝ) : Prop :=
  AGT.IsMixedNash (S := fun _ : Fin n => Fin m) (payoff w) p

/-- The expected cost `c_i` of agent `i` under the mixed profile `p`: the expected traffic on the link
agent `i` chooses, links being chosen independently with the probabilities `p` (PDF p. 2). -/
def expCost (w : Fin n → ℝ) (p : Fin n → Fin m → ℝ) (i : Fin n) : ℝ :=
  -AGT.expectedPayoff (S := fun _ : Fin n => Fin m) (payoff w) p i

/-- The expected traffic `M^j = ∑_i p_i^j w_i` on link `j`, (1) (PDF p. 3). -/
def expTraffic (w : Fin n → ℝ) (p : Fin n → Fin m → ℝ) (j : Fin m) : ℝ :=
  ∑ i, p i j * w i

/-- The cost `c_i^j = w_i + ∑_{k ≠ i} p_k^j w_k` of agent `i` when its own traffic is assigned to link
`j`, first form of (2) (PDF p. 3). -/
def linkCost (w : Fin n → ℝ) (p : Fin n → Fin m → ℝ) (i : Fin n) (j : Fin m) : ℝ :=
  w i + ∑ k ∈ Finset.univ.erase i, p k j * w k

/-- The pure strategy "link `j`" as a lottery: probability `1` on `j`, `0` elsewhere. -/
def pureLottery (j : Fin m) : Fin m → ℝ :=
  fun j' => if j' = j then 1 else 0

/-- The collision probability `t_ik = ∑_j p_i^j p_k^j` of agents `i` and `k` (proof of Theorem 3,
PDF p. 5). -/
def collisionProb (p : Fin n → Fin m → ℝ) (i k : Fin n) : ℝ :=
  ∑ j, p i j * p k j

section Links

variable [NeZero m]

/-- The maximum traffic `max_{j} ∑_{k : j_k = j} w_k` over all links under the pure profile `s`
(the makespan of the assignment `s`). -/
def makespan (w : Fin n → ℝ) (s : Fin n → Fin m) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (load w s)

/-- The social cost (4) (PDF p. 4): the expected maximum traffic over all links,
`∑_{j_1} ⋯ ∑_{j_n} ∏_i p_i^{j_i} · max_j ∑_{k : j_k = j} w_k`. -/
def socialCost (w : Fin n → ℝ) (p : Fin n → Fin m → ℝ) : ℝ :=
  ∑ s : Fin n → Fin m, AGT.profileProb (S := fun _ : Fin n => Fin m) p s * makespan w s

/-- The social optimum `opt`: the optimum of the `m`-way load balancing problem, i.e. the least makespan
over all pure assignments of the `n` agents to the `m` links (PDF p. 2). The number of links `m` is an
explicit argument, since `w` does not determine it. -/
def opt (m : ℕ) [NeZero m] (w : Fin n → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (makespan (m := m) w)

/-- Link `j` is the lexicographically first link of maximum load under the pure profile `s`
(proof of Theorem 3, PDF p. 5). -/
def IsFirstMaxLink (w : Fin n → ℝ) (s : Fin n → Fin m) (j : Fin m) : Prop :=
  load w s j = makespan w s ∧ ∀ j', j' < j → load w s j' < makespan w s

open Classical in
/-- The contribution probability `q_i` of agent `i`: the probability that its traffic goes to the
(lexicographically first) link of maximum load (proof of Theorem 3, PDF p. 5). -/
def contribProb (w : Fin n → ℝ) (p : Fin n → Fin m → ℝ) (i : Fin n) : ℝ :=
  ∑ s : Fin n → Fin m, AGT.profileProb (S := fun _ : Fin n => Fin m) p s *
    (if IsFirstMaxLink w s (s i) then 1 else 0)

end Links

end

end WorstCaseEq.Identical


