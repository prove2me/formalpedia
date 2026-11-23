-- Prove2me | Definitions.Def_BayesGroupHard_VertexCover_Supplement_Decision
-- name    : BayesGroupHard_VertexCover_Supplement_Decision
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:40:40.299054+00:00
-- url     : https://prove2.me/theorems/1bd37b2a-ec99-435d-a0f6-76308fc32f8a
-- title:
--   Problem 2, p. 8 — GROUP-DECISION with revealed beliefs at t = 2: rational instances, binary code, decision language and the two exponentially-small-belief sides
-- statement:
--   **GROUP-DECISION with revealed beliefs (Problem 2, p. 8), at time $t=2$.** An instance consists of a number $n$ of agents, neighbourhoods $\mathcal N_j\ni j$, rational signal structures $\mathbb P_{j,\theta}(1)\in[0,1]\cap\mathbb Q$ for every agent $j$ and state $\theta\in\{0,1\}$, a distinguished agent $i$, her own signal $s_i$, and the rational beliefs $\mu_{j,0}(1)$, $\mu_{j,1}(1)$ reported by her neighbours $j\in\mathcal N_i$ at times $0$ and $1$. The prior is uniform. The profiles consistent with the instance are
--   $$\mathcal I=\{s : s_i \text{ as given and } r_{j,\tau}(s)=\text{the given report for all } j\in\mathcal N_i,\ \tau\in\{0,1\}\},$$
--   with $r_{j,\tau}$ the revealed-belief dynamics; the instance is **valid** when $\mathcal I$ has positive probability, and the answer is the posterior $\mu_{i,2}(\theta)=\mu(\theta\mid\mathcal I)$.
--
--   Instances are written as bit strings: a self-delimiting binary code of the agent count, the adjacency matrix, each rational as sign, numerator and denominator, the index of $i$, her signal, and the neighbours' reports. The **decision language** consists of the codes of valid instances with $\mu_{i,2}(1)<\mu_{i,2}(0)$. For $c>0$ and a threshold $N$, the **side** $\theta$ consists of the codes of valid instances with at least $N$ agents and
--   $$\mu_{i,2}(\theta)\le \exp(-c\cdot \#\text{agents}).$$
--
--   These are the problems of Theorem 2: NP-hardness of computing the posterior, and of distinguishing the two sides.
--
--   **Formalization Note.** `DecisionInstance`, `decisionCode`, `Valid`, `posterior`, `decisionLanguage`, `smallBelief θ c N`. Languages are `CookPvsNP.Lang Bool` over the platform's one-tape Turing-machine model. Reports of non-neighbours of $i$ are carried by the structure but neither encoded nor used. Deterministic signal structures ($0$ or $1$) are allowed; validity excludes impossible histories.
-- source:
--   Hązła, Jadbabaie, Mossel & Rahimian, Bayesian Decision Making in Groups is Hard, arXiv:1705.04770v4, p. 8 (Problem 2), p. 7 (§2.1, revealed belief model), p. 11 (Theorem 2)

import Mathlib
import Definitions.Def_BayesGroupHard_VertexCover_Supplement_Dynamics
import Definitions.Def_MeanBudgetXC_Supplement_PromiseNPHard
import Definitions.Def_KingTerrain_NPHard_Complexity

namespace BayesGroupHard.VertexCover.Supplement

open Finset
/-- Rational, binary-state, binary-signal input at time two. All rational probabilities
in [0,1] are allowed, including deterministic signals. Histories specify the own signal
and two rounds of rational reports from each neighbour. -/
structure DecisionInstance where
  agents : ℕ
  nbr : Fin agents → Finset (Fin agents)
  self_mem : ∀ j, j ∈ nbr j
  prob : Fin agents → Bool → ℚ
  prob_bounds : ∀ j θ, 0 ≤ prob j θ ∧ prob j θ ≤ 1
  target : Fin agents
  ownSignal : Bool
  history : Fin agents → Fin 2 → ℚ

def DecisionInstance.net (D : DecisionInstance) : BinNet (Fin D.agents) where
  nbr := D.nbr
  self_mem := D.self_mem
  p j θ := (D.prob j θ : ℝ)

noncomputable def DecisionInstance.info (D : DecisionInstance) : Finset (Fin D.agents → Bool) := by
  classical
  exact univ.filter (fun s => s D.target = D.ownSignal ∧
    ∀ j ∈ D.nbr D.target, ∀ t : Fin 2,
      report D.net t.val j s = (D.history j t : ℝ))

/-- Positive prior likelihood of the history; impossible histories are not instances. -/
def DecisionInstance.Valid (D : DecisionInstance) : Prop :=
  0 < (∑ s ∈ D.info, jointProb D.net false s) +
    (∑ s ∈ D.info, jointProb D.net true s)

noncomputable def DecisionInstance.posterior (D : DecisionInstance) (θ : Bool) : ℝ :=
  post D.net θ D.info

/-- Self-delimiting binary natural: unary bit-length, a zero separator, then little-endian bits. -/
def encNat (n : ℕ) : List Bool :=
  let bs := (Nat.digits 2 n).map (fun b => decide (b = 1))
  List.replicate bs.length true ++ [false] ++ bs

/-- Canonical rational: sign bit, absolute numerator, positive denominator. -/
def encRat (q : ℚ) : List Bool :=
  [decide (q.num < 0)] ++ encNat q.num.natAbs ++ encNat q.den

/-- An adjacency matrix, two probabilities per agent, target and own signal, then
both reports of each neighbour in increasing index order. No posterior is encoded. -/
def decisionCode (D : DecisionInstance) : List Bool :=
  let inds := List.finRange D.agents
  encNat D.agents ++
    inds.flatMap (fun j => inds.map (fun k => decide (k ∈ D.nbr j))) ++
    inds.flatMap (fun j => encRat (D.prob j false) ++ encRat (D.prob j true)) ++
    encNat D.target.val ++ [D.ownSignal] ++
    (inds.filter (fun j => decide (j ∈ D.nbr D.target))).flatMap
      (fun j => encRat (D.history j 0) ++ encRat (D.history j 1))

/-- Decision version: is state 0 strictly more likely than state 1? -/
def decisionLanguage : CookPvsNP.Lang Bool :=
  {w | ∃ D : DecisionInstance, w = decisionCode D ∧ D.Valid ∧
    D.posterior true < D.posterior false}

/-- The θ belief is exponentially small. The number in the exponent is #agents. -/
def smallBelief (θ : Bool) (c : ℝ) (N : ℕ) : Set (List Bool) :=
  {w | ∃ D : DecisionInstance, w = decisionCode D ∧ D.Valid ∧ N ≤ D.agents ∧
    D.posterior θ ≤ Real.exp (-c * (D.agents : ℝ))}

end BayesGroupHard.VertexCover.Supplement


