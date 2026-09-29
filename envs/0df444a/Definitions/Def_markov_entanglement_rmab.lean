-- Prove2me | Definitions.Def_markov_entanglement_rmab
-- name    : markov_entanglement_rmab
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-08-10T23:47:08.130722+00:00
-- url     : https://prove2.me/theorems/66561d0c-b957-4194-9e0f-fcd6a44b3d9a
-- title:
--   Restless multi-armed bandits, index policies and the mean-field limit
-- statement:
--   The restless-bandit vocabulary: homogeneous agents, two actions, a budget, and the mean-field objects the asymptotic theory is stated in.
--
--   A restless multi-armed bandit (Definition 12) is the weakly-coupled MDP of `markov_entanglement_policy` specialised in three ways. The agents are **homogeneous**, sharing one local state space, one pair of local kernels $\{P_0,P_1\}$ and one pair of rewards. Each agent has exactly **two actions**, idle and activate. The coupling is a **budget**: exactly $M$ of the $N$ agents are activated at each step.
--
--   Homogeneity is what makes the asymptotic analysis possible. The joint state is a plain function $\{1,\dots,N\}\to S$, and its natural summary is the **configuration** $m \in \Delta^{|S|}$, the fraction of agents in each local state. The entire theory is a statement about that configuration: as $N \to \infty$ it concentrates on a mean-field fixed point $m^\ast$, each agent's transition comes to depend only on its own state, the system decouples, and the measure of Markov entanglement vanishes at rate $1/\sqrt{N}$.
--
--   What is defined:
--
--   * `stateCount`, `configuration`, `IsConfiguration` — how many agents sit in a state, the resulting point of the simplex, and what it means to be such a point.
--   * `rmabKernel`, `rmabReward` — the two local kernels and rewards, indexed by the action, so that an RMAB instantiates `IsWeaklyCoupled` directly.
--   * `IsBudgeted` — exactly $M$ agents activated.
--   * `higherPriorityCount`, `activateCount`, `indexActivationProb` — Definition 13 made precise. An index policy serves states in descending order of the priority $\nu$ until the budget runs out; `activateCount` is the budget remaining once every strictly higher-priority state has been served, capped by how many agents are actually present, and `indexActivationProb` spreads that uniformly over the agents in the state, which is what "ties resolved by uniform sampling" amounts to for a single agent.
--   * `IsIndexPolicy` — a joint policy supported on budgeted actions whose agent marginals are exactly those uniform activation probabilities.
--   * `IsMeanFieldMap`, `meanFieldIterate` — the configuration's expected one-step transition $\varphi(m) = \mathbb E[m[t+1] \mid m[t]=m]$ and its iterates. It is *characterised* rather than constructed, so that the assumptions below can be stated without first building the $N$-agent chain.
--   * `supNorm`, `IsUniformGlobalAttractor`, `IsNonDegenerate` — Assumptions 1 and 2. UGAP says $m^\ast$ attracts every initial configuration uniformly in the starting point, which rules out chaos in the limit and forces the fixed point to be unique; non-degeneracy says some state is served only fractionally at $m^\ast$, so the limiting policy genuinely randomises there, which rules out cycling.
--
--   These two assumptions are not peculiar to this paper — they are the standard hypotheses under which index policies are analysed, going back to Weber and Weiss (1990) and used throughout Verloop (2016) and Gast et al. (2023, 2024).
--
--   ## Relation to the platform's other bandit vocabulary
--
--   The platform's `GittinsIndex` definition formalizes the *classical* discounted $k$-armed Markov bandit of Lattimore and Szepesvári §35.4, where only the activated arm changes state and a single arm is activated at each round by maximal index. A **restless** bandit differs on both counts: every arm moves at every step, whether activated or not, and a budget of $M$ arms is activated simultaneously, chosen by priority with ties broken uniformly. The Gittins index is the historical ancestor of the priority indices used here — Definition 13 says so explicitly — but the two models are not instances of one another, so this file does not build on it.
--
--   Likewise the single-agent `FiniteMDPLearning` layer (`BanditAlgorithm.FiniteMDP`) is not a base for this file; see the discussion under `markov_entanglement_policy`, which this file extends.
-- source:
--   Shuze Chen and Tianyi Peng, 'Multi-agent Markov Entanglement', arXiv:2506.02385v3, Definitions 12 and 13 (pp. 23-24), Assumptions 1 and 2 (p. 41)

import Definitions.Def_markov_entanglement_policy

open scoped BigOperators

namespace MarkovEntanglement

/-! ## Restless multi-armed bandits and index policies

A restless multi-armed bandit is the weakly-coupled MDP of `Def_markov_entanglement_policy`
specialised in three ways (Definition 12): the agents are **homogeneous**, so they share one
local state space, one pair of local kernels and one pair of rewards; each agent has exactly
**two actions**, idle and activate; and the coupling is a **budget** — exactly `M` of the `N`
agents are activated at every step.

Because the agents are homogeneous, the joint state is a plain function `Fin N → S` rather
than a dependent product, and the natural summary of a joint state is its **configuration**,
the fraction of agents sitting in each local state.  The whole asymptotic theory is a
statement about that configuration: as `N → ∞` it concentrates on a mean-field fixed point,
the system decouples, and the measure of Markov entanglement vanishes. -/

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The number of agents sitting in local state `x`. -/
def stateCount {N : ℕ} (s : Fin N → S) (x : S) : ℕ :=
  (Finset.univ.filter fun i => s i = x).card

/-- The **configuration** of a joint state: the fraction of agents in each local state.
This is the object the mean-field analysis follows. -/
noncomputable def configuration {N : ℕ} (s : Fin N → S) (x : S) : ℝ :=
  (stateCount s x : ℝ) / (N : ℝ)

/-- A point of the simplex `Δ^{|S|}`, the space configurations live in. -/
def IsConfiguration (m : S → ℝ) : Prop := (∀ x, 0 ≤ m x) ∧ ∑ x, m x = 1

/-- The two local kernels of an RMAB, packaged as one kernel indexed by the action:
`false` is idle, `true` is activate. -/
def rmabKernel (P0 P1 : Matrix S S ℝ) (x : S) (a : Bool) (y : S) : ℝ :=
  if a then P1 x y else P0 x y

/-- The two local rewards of an RMAB. -/
def rmabReward (r0 r1 : S → ℝ) (x : S) (a : Bool) : ℝ := if a then r1 x else r0 x

/-- The **budget constraint**: exactly `M` of the `N` agents are activated. -/
def IsBudgeted {N : ℕ} (M : ℕ) (a : Fin N → Bool) : Prop :=
  (Finset.univ.filter fun i => a i = true).card = M

/-- The number of agents in states of strictly higher priority than `x`. -/
noncomputable def higherPriorityCount {N : ℕ} (ν : S → ℝ) (s : Fin N → S) (x : S) : ℕ :=
  ∑ y ∈ Finset.univ.filter fun y => ν x < ν y, stateCount s y

/-- How many of the agents sitting in state `x` an index policy activates: the budget left
after every strictly higher-priority state has been served, capped by how many agents are
actually in `x`.  This is the content of "activate in descending order of priority until the
budget is met" (Definition 13). -/
noncomputable def activateCount {N : ℕ} (ν : S → ℝ) (M : ℕ) (s : Fin N → S) (x : S) : ℕ :=
  min (stateCount s x) (M - higherPriorityCount ν s x)

/-- The probability that an index policy activates a given agent sitting in state `x`:
the agents in a state are exchangeable, so the activation is spread uniformly over them.
Zero when no agent is in `x`. -/
noncomputable def indexActivationProb {N : ℕ} (ν : S → ℝ) (M : ℕ)
    (s : Fin N → S) (x : S) : ℝ :=
  if stateCount s x = 0 then 0 else (activateCount ν M s x : ℝ) / (stateCount s x : ℝ)

/-- `π` is an **index policy** for priority index `ν` and budget `M`: it is a joint policy,
it only ever plays budgeted joint actions, and — the agents in a state being exchangeable —
each agent is activated with the uniform probability `indexActivationProb`. -/
def IsIndexPolicy {N : ℕ} (ν : S → ℝ) (M : ℕ)
    (π : (Fin N → S) → (Fin N → Bool) → ℝ) : Prop :=
  IsJointPolicy (St := fun _ => S) (Act := fun _ => Bool) π ∧
    (∀ s a, π s a ≠ 0 → IsBudgeted M a) ∧
    (∀ s i, policyMarginal (St := fun _ => S) (Act := fun _ => Bool) i π s true
      = indexActivationProb ν M s (s i))

/-- `φ` is the **mean-field transition map** of the configuration under the policy: the
expected next configuration given the current one, `φ(m) = E[m[t+1] ∣ m[t] = m, π]`.  It is
characterised rather than constructed, so that the assumptions below can be stated for it
without first building the `N`-agent chain. -/
def IsMeanFieldMap {N : ℕ} (P0 P1 : Matrix S S ℝ) (ν : S → ℝ) (M : ℕ)
    (φ : (S → ℝ) → (S → ℝ)) : Prop :=
  ∀ s : Fin N → S, ∀ y : S,
    φ (configuration s) y
      = ∑ i : Fin N, (1 / (N : ℝ)) *
          ((1 - indexActivationProb ν M s (s i)) * P0 (s i) y
            + indexActivationProb ν M s (s i) * P1 (s i) y)

/-- Iterating the mean-field map. -/
def meanFieldIterate (φ : (S → ℝ) → (S → ℝ)) : ℕ → (S → ℝ) → (S → ℝ)
  | 0, m => m
  | (t + 1), m => φ (meanFieldIterate φ t m)

/-- The supremum norm on configurations. -/
noncomputable def supNorm (m : S → ℝ) : ℝ := ⨆ x : S, |m x|

/-- **Uniform Global Attractor Property** (Assumption 1): `m✦` attracts every initial
configuration, uniformly in the initial point.  This is what rules out chaotic behaviour in
the mean-field limit and forces the fixed point to be unique. -/
def IsUniformGlobalAttractor (φ : (S → ℝ) → (S → ℝ)) (mstar : S → ℝ) : Prop :=
  φ mstar = mstar ∧
    ∀ ε > 0, ∃ T : ℕ, ∀ t ≥ T, ∀ m : S → ℝ, IsConfiguration m →
      supNorm (fun x => meanFieldIterate φ t m x - mstar x) < ε

/-- **Non-degeneracy** (Assumption 2): at the mean-field fixed point some state is served
only fractionally, so the limiting policy genuinely randomises there.  This rules out cyclic
behaviour in the limit. -/
def IsNonDegenerate (ν : S → ℝ) (M : ℕ) (mstar : S → ℝ) (N : ℕ) : Prop :=
  ∃ x : S, 0 < mstar x ∧
    0 < (M : ℝ) - ∑ y ∈ Finset.univ.filter fun y => ν x < ν y, (N : ℝ) * mstar y ∧
    (M : ℝ) - ∑ y ∈ Finset.univ.filter fun y => ν x < ν y, (N : ℝ) * mstar y
      < (N : ℝ) * mstar x

end MarkovEntanglement


