-- Prove2me | Definitions.Def_markov_entanglement_policy
-- name    : markov_entanglement_policy
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-08-10T13:54:19.59767+00:00
-- url     : https://prove2.me/theorems/4e68c90d-b827-4af1-aabb-d10fc0482a6a
-- title:
--   States, actions and policies for multi-agent MDPs
-- statement:
--   Adds states, actions and policies as first-class objects, which everything from Section 7 of the source onwards requires.
--
--   The entanglement vocabulary so far runs over one index type per agent, playing the role of that agent's *state-action pair*. That is enough for Theorems 1-6, 8, 9, whose statements never mention a policy. It is not enough for weakly-coupled MDPs, restless bandits or index policies: there the bounds are stated in terms of how far a joint policy sits from a **local** policy, one that reads only its own agent's state, so states, actions and policies have to be separate.
--
--   This file supplies that layer and, importantly, connects it back rather than starting over. Agent $i$'s state-action space is $S_i \times A_i$, so the joint state-action space is exactly the index type the existing definitions consume; `entanglementN`, `muAgentTVDistN`, `marginalN` and the rest apply verbatim to the transition matrix induced by a kernel and a policy.
--
--   What is added:
--
--   * `JointState`, `JointAction`, `StateAction` — the three index types, and `splitStateAction`, the equivalence turning a sum over joint state-action pairs into an iterated sum over joint states and joint actions.
--   * `IsJointPolicy`, `IsLocalPolicy` — randomised policies over joint and over local actions.
--   * `policyMarginal` — agent $i$'s action marginal of a joint policy, $\pi(a_i \mid s)$.
--   * `IsWeaklyCoupled`, `IsLocalKernel` — Definition 11: each agent's next state depends only on its own state and action, $P(s' \mid s,a) = \prod_i P_i(s'_i \mid s_i, a_i)$. Agents remain coupled through the policy, and in applications through constraints on the joint action, but never through the transition.
--   * `inducedTransition` — the state-action transition $P^\pi$: move the state with $P$, then draw the next action from $\pi$ at the new state. This is the matrix the entanglement theory is applied to.
--   * `occupancyStateMarginal` — the state marginal of an occupancy measure carried on state-action pairs.
--   * `policyMismatch` and `leastPolicyMismatch` — $\tfrac12 \sum_s \mu(s) \sum_{a_i} \lvert \pi(a_i \mid s) - \pi'(a_i \mid s_i) \rvert$, the quantity that bounds the measure of Markov entanglement in a weakly-coupled system, before and after minimising over the local policy $\pi'$.
--
--   The design intent is reuse: none of this is specific to Markov entanglement. Any formalization of multi-agent MDPs, weakly-coupled MDPs, restless bandits or factored MDPs needs joint and local policies, action marginals and product transition kernels, and can take them from here.
--
--   ## Relation to the platform's other MDP vocabulary
--
--   The platform already carries a finite-MDP layer, `FiniteMDPLearning` (`BanditAlgorithm.FiniteMDP`, from Lattimore and Szepesvári Ch. 38), and a classical Markov-bandit layer, `GittinsIndex` (§35.4). This file deliberately does **not** build on either, and the reason is structural rather than stylistic:
--
--   * `FiniteMDP` is **single-agent**. The entanglement theory is about how a joint transition factorises across agents, so it needs per-agent state and action spaces, per-agent marginals and per-agent measures of entanglement. Collapsing the agents into one state space `Fin S` would leave that vocabulary with nothing to refer to.
--   * `FiniteMDP` takes transition probabilities in `ℝ≥0`. Separability is defined by an **affine** hull — finite combinations $\sum_k x_k P^{(k)}$ with $\sum_k x_k = 1$ and the $x_k$ allowed to be negative — so nonnegativity is the wrong ambient type here.
--   * Its policies are history-dependent Markov kernels and its semantics is a measure on trajectories. The results here are about the induced state-action transition matrix and its stationary distribution, and are proved by finite sums; no trajectory measure is needed.
--   * Its rewards are constrained to $[0,1]$; here they are signed and bounded by a per-agent $r^i_{\max}$.
--
--   `GittinsIndex` is closer in subject — the index policies of Definition 13 trace back to the Gittins index — but models a *classical* bandit, in which only the activated arm moves and a single arm is activated by maximal index. A restless bandit moves every arm at every step and activates $M$ of them by priority, so the two are related models rather than instances of one another.
--
--   Anyone formalizing single-agent online learning in MDPs should prefer `FiniteMDPLearning`; this file is for the multi-agent, occupancy-measure side of the theory.
-- source:
--   Shuze Chen and Tianyi Peng, 'Multi-agent Markov Entanglement', arXiv:2506.02385v3, Section 7.1, Definition 11 (p. 22) and Proposition 1 (p. 22)

import Definitions.Def_markov_entanglement_multi

open scoped BigOperators

namespace MarkovEntanglement

/-! ## States, actions and policies

The entanglement vocabulary so far works with transition matrices on a single index
type per agent, which plays the role of that agent's *state-action pair*.  Everything
from Section 7 of the source onwards — weakly-coupled MDPs, restless bandits, index
policies — needs states and actions to be separate objects and needs a policy as a
first-class citizen, because the bounds there are stated in terms of how far a joint
policy sits from a *local* one.

This file adds that layer and connects it back: the state-action space `StateAction`
is exactly the index type the existing definitions consume, so `entanglementN`,
`muAgentTVDistN` and friends apply verbatim to `inducedTransition P π`. -/

variable {N : ℕ} {St Act : Fin N → Type*}

/-- The joint state space of `N` agents. -/
abbrev JointState (St : Fin N → Type*) : Type _ := ∀ i, St i

/-- The joint action space of `N` agents. -/
abbrev JointAction (Act : Fin N → Type*) : Type _ := ∀ i, Act i

/-- Agent `i`'s state-action space.  `Joint (StateAction St Act)` is the joint
state-action space, which is the index type the entanglement definitions run over. -/
abbrev StateAction (St Act : Fin N → Type*) : Fin N → Type _ := fun i => St i × Act i

/-- Splitting a joint state-action pair into its state part and its action part.
Used to turn sums over the joint state-action space into iterated sums over joint
states and joint actions. -/
def splitStateAction : (Joint (StateAction St Act)) ≃ JointState St × JointAction Act where
  toFun p := (fun i => (p i).1, fun i => (p i).2)
  invFun x := fun i => (x.1 i, x.2 i)
  left_inv p := by funext i; rfl
  right_inv x := rfl

/-- A randomised **joint policy**: a distribution over joint actions at each joint state. -/
def IsJointPolicy [∀ i, Fintype (Act i)]
    (π : JointState St → JointAction Act → ℝ) : Prop :=
  (∀ s a, 0 ≤ π s a) ∧ ∀ s, ∑ a, π s a = 1

/-- A randomised **local policy** for agent `i`: a distribution over that agent's own
actions at each of its own states. -/
def IsLocalPolicy {i : Fin N} [Fintype (Act i)] (πl : St i → Act i → ℝ) : Prop :=
  (∀ s a, 0 ≤ πl s a) ∧ ∀ s, ∑ a, πl s a = 1

/-- Agent `i`'s action marginal of a joint policy: the probability that agent `i`
plays `ai` at the joint state `s`. -/
def policyMarginal [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
    (i : Fin N) (π : JointState St → JointAction Act → ℝ)
    (s : JointState St) (ai : Act i) : ℝ :=
  ∑ a : JointAction Act, if a i = ai then π s a else 0

/-- A joint kernel is **weakly coupled** when each agent's next state depends only on
that agent's own state and action, `P(s' ∣ s,a) = ∏ i, Pᵢ(s'ᵢ ∣ sᵢ,aᵢ)` (Definition 11).
The agents are still coupled — through the policy, and in applications through
constraints on the joint action — but never through the transition. -/
def IsWeaklyCoupled [∀ i, Fintype (St i)]
    (P : JointState St → JointAction Act → JointState St → ℝ)
    (Pl : ∀ i, St i → Act i → St i → ℝ) : Prop :=
  ∀ s a s', P s a s' = ∏ i, Pl i (s i) (a i) (s' i)

/-- Each local kernel is a transition kernel. -/
def IsLocalKernel [∀ i, Fintype (St i)] (Pl : ∀ i, St i → Act i → St i → ℝ) : Prop :=
  (∀ i s a s', 0 ≤ Pl i s a s') ∧ ∀ i s a, ∑ s', Pl i s a s' = 1

/-- The transition matrix on **state-action pairs** induced by a kernel and a policy:
move the state with `P`, then draw the next action from `π` at the new state.  This is
the matrix the whole entanglement theory is applied to. -/
def inducedTransition [∀ i, Fintype (St i)] [∀ i, Fintype (Act i)]
    (P : JointState St → JointAction Act → JointState St → ℝ)
    (π : JointState St → JointAction Act → ℝ) :
    Matrix (Joint (StateAction St Act)) (Joint (StateAction St Act)) ℝ :=
  fun p q => P (fun i => (p i).1) (fun i => (p i).2) (fun i => (q i).1)
    * π (fun i => (q i).1) (fun i => (q i).2)

/-- The state marginal of an occupancy measure carried on state-action pairs. -/
def occupancyStateMarginal [∀ i, Fintype (St i)] [∀ i, Fintype (Act i)]
    [∀ i, DecidableEq (St i)]
    (μ : Joint (StateAction St Act) → ℝ) (s : JointState St) : ℝ :=
  ∑ p : Joint (StateAction St Act), if (fun i => (p i).1) = s then μ p else 0

/-- The **policy mismatch** of agent `i` against a local policy `πl`: how far the joint
policy's action marginal for agent `i` sits from a policy that reads only agent `i`'s own
state, averaged over the occupancy measure.  This is the right-hand side of the
weakly-coupled bound (Proposition 1) before the minimisation over `πl`. -/
noncomputable def policyMismatch [∀ i, Fintype (St i)] [∀ i, Fintype (Act i)]
    [∀ i, DecidableEq (St i)] [∀ i, DecidableEq (Act i)]
    (i : Fin N) (π : JointState St → JointAction Act → ℝ)
    (μ : Joint (StateAction St Act) → ℝ) (πl : St i → Act i → ℝ) : ℝ :=
  (1 / 2) * ∑ s : JointState St, occupancyStateMarginal μ s *
    ∑ ai : Act i, |policyMarginal i π s ai - πl (s i) ai|

/-- The least policy mismatch attainable by a local policy for agent `i`. -/
noncomputable def leastPolicyMismatch [∀ i, Fintype (St i)] [∀ i, Fintype (Act i)]
    [∀ i, DecidableEq (St i)] [∀ i, DecidableEq (Act i)]
    (i : Fin N) (π : JointState St → JointAction Act → ℝ)
    (μ : Joint (StateAction St Act) → ℝ) : ℝ :=
  sInf {c : ℝ | ∃ πl : St i → Act i → ℝ, IsLocalPolicy πl ∧ c = policyMismatch i π μ πl}

end MarkovEntanglement


