-- Prove2me | Definitions.Def_BayesGroupHard_VertexCover_Supplement_BinaryDecision
-- name    : BayesGroupHard_VertexCover_Supplement_BinaryDecision
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:41:22.579596+00:00
-- url     : https://prove2.me/theorems/413207e6-4b2a-41c7-aa99-f0bfb2502aea
-- title:
--   Problem 1, p. 7 — GROUP-DECISION in the binary action model at t = 2: rational instances, binary code, decision language and the two exponentially-small-belief sides
-- statement:
--   **GROUP-DECISION in the binary action model (Problem 1, p. 7, with §2.1), at time $t=2$.** An instance consists of a number $n$ of agents, neighbourhoods $\mathcal N_j\ni j$, rational signal structures $\mathbb P_{j,\theta}(1)\in[0,1]\cap\mathbb Q$ for every agent $j$ and state $\theta\in\{0,1\}$, a distinguished agent $i$, her own signal $s_i$, and the binary actions $a_{j,0},a_{j,1}\in\{0,1\}$ taken by her neighbours $j\in\mathcal N_i$ at times $0$ and $1$. The prior is uniform, and every agent's action is her MAP estimate of $\theta$, ties going to $0$ (the binary action model of §2.1, with the tie-breaking rule of p. 6). The profiles consistent with the instance are
--   $$\mathcal I=\{s : s_i \text{ as given and } a_{j,\tau}(s)=\text{the given action for all } j\in\mathcal N_i,\ \tau\in\{0,1\}\},$$
--   with $a_{j,\tau}$ the binary-action dynamics of the published model; the instance is **valid** when $\mathcal I$ has positive probability. Its posterior is $\mu_{i,2}(\theta)=\mu(\theta\mid\mathcal I)$ and its answer is the Bayesian action $a_{i,2}$, the MAP estimate under $\mu_{i,2}$.
--
--   Instances are written as bit strings: a self-delimiting binary code of the agent count, the adjacency matrix, each rational as sign, numerator and denominator, the index of $i$, her signal, and the neighbours' two actions. The **decision language** consists of the codes of valid instances with $a_{i,2}=0$. For $c>0$ and a threshold $N$, the **side** $\theta$ consists of the codes of valid instances with at least $N$ agents and
--   $$\mu_{i,2}(\theta)< \exp(-c\cdot \#\text{agents}).$$
--
--   These are the problems of Theorem 1: NP-hardness of computing the Bayesian action at $t=2$, and of distinguishing the two sides.
--
--   **Formalization Note.** `BinDecisionInstance`, `binDecisionCode`, `Valid`, `posterior`, `action`, `binDecisionLanguage`, `binSmallBelief θ c N`. The dynamics (`act`, `mapAct`, `post`, `BinNet`) are those of the published `BayesGroupHard.VertexCover.Model`; the codes of naturals and rationals (`encNat`, `encRat`) are those of the revealed-belief `Decision` definition. Languages are `CookPvsNP.Lang Bool` over the platform's one-tape Turing-machine model. Actions of non-neighbours of $i$ are carried by the structure but neither encoded nor used. Deterministic signal structures ($0$ or $1$) are allowed; validity excludes impossible histories.
-- source:
--   Hązła, Jadbabaie, Mossel & Rahimian, Bayesian Decision Making in Groups is Hard, arXiv:1705.04770v4, p. 6 (§2, (1), tie-breaking), p. 7 (Problem 1, §2.1 binary action model), p. 9 (Theorem 1)

import Mathlib
import Definitions.Def_BayesGroupHard_VertexCover_Supplement_Decision

namespace BayesGroupHard.VertexCover.Supplement

open Finset
/-- Problem 1 (GROUP-DECISION, p. 7) in the binary action model at time two: rational,
binary-state, binary-signal input. All rational probabilities in [0,1] are allowed, including
deterministic signals. Histories specify the own signal and the binary actions of each
neighbour at times 0 and 1. -/
structure BinDecisionInstance where
  agents : ℕ
  nbr : Fin agents → Finset (Fin agents)
  self_mem : ∀ j, j ∈ nbr j
  prob : Fin agents → Bool → ℚ
  prob_bounds : ∀ j θ, 0 ≤ prob j θ ∧ prob j θ ≤ 1
  target : Fin agents
  ownSignal : Bool
  history : Fin agents → Fin 2 → Bool

def BinDecisionInstance.net (D : BinDecisionInstance) : BinNet (Fin D.agents) where
  nbr := D.nbr
  self_mem := D.self_mem
  p j θ := (D.prob j θ : ℝ)

/-- The signal profiles consistent with the history: the target's own signal and the
MAP actions `a_{j,τ}` (binary action model, ties to `false`) of her neighbours at `τ = 0, 1`. -/
noncomputable def BinDecisionInstance.info (D : BinDecisionInstance) :
    Finset (Fin D.agents → Bool) := by
  classical
  exact univ.filter (fun s => s D.target = D.ownSignal ∧
    ∀ j ∈ D.nbr D.target, ∀ t : Fin 2, act D.net t.val j s = D.history j t)

/-- Positive prior likelihood of the history; impossible histories are not instances. -/
def BinDecisionInstance.Valid (D : BinDecisionInstance) : Prop :=
  0 < (∑ s ∈ D.info, jointProb D.net false s) +
    (∑ s ∈ D.info, jointProb D.net true s)

/-- The posterior `µ_{i,2}(θ)` of the target agent. -/
noncomputable def BinDecisionInstance.posterior (D : BinDecisionInstance) (θ : Bool) : ℝ :=
  post D.net θ D.info

/-- The Bayesian action `a_{i,2}` of the target agent (MAP, ties to `false`). -/
noncomputable def BinDecisionInstance.action (D : BinDecisionInstance) : Bool :=
  mapAct D.net D.info

/-- An adjacency matrix, two probabilities per agent, target and own signal, then both
actions of each neighbour in increasing index order. No posterior or action is encoded. -/
def binDecisionCode (D : BinDecisionInstance) : List Bool :=
  let inds := List.finRange D.agents
  encNat D.agents ++
    inds.flatMap (fun j => inds.map (fun k => decide (k ∈ D.nbr j))) ++
    inds.flatMap (fun j => encRat (D.prob j false) ++ encRat (D.prob j true)) ++
    encNat D.target.val ++ [D.ownSignal] ++
    (inds.filter (fun j => decide (j ∈ D.nbr D.target))).flatMap
      (fun j => [D.history j 0, D.history j 1])

/-- Decision version: is the Bayesian action `a_{i,2}` equal to `0`? -/
def binDecisionLanguage : CookPvsNP.Lang Bool :=
  {w | ∃ D : BinDecisionInstance, w = binDecisionCode D ∧ D.Valid ∧ D.action = false}

/-- The θ belief is exponentially small (strictly). The number in the exponent is #agents. -/
def binSmallBelief (θ : Bool) (c : ℝ) (N : ℕ) : Set (List Bool) :=
  {w | ∃ D : BinDecisionInstance, w = binDecisionCode D ∧ D.Valid ∧ N ≤ D.agents ∧
    D.posterior θ < Real.exp (-c * (D.agents : ℝ))}

end BayesGroupHard.VertexCover.Supplement


