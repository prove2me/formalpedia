-- Prove2me | Definitions.Def_SelfAdaptingFNR_WDP
-- name    : SelfAdaptingFNR_WDP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:37:10.796064+00:00
-- url     : https://prove2.me/theorems/df08f55c-9365-405c-b883-31189d0a0322
-- title:
--   Weakly coupled Markov decision process: components, linking constraints, $\mathcal A_t(s)$, $\mathscr F_t$
-- statement:
--   A **weakly coupled Markov decision process (WDP)** consists of $J$ component MDPs indexed by $\mathcal J=\{1,\dots,J\}$ that share the decision periods $\mathcal T=\{0,\dots,T-1\}$ and a terminal period $T$. In period $t$ component $j$ is in a state $s_j$ of a finite state space $\mathcal S_{t,j}$, applies an action $a_j$ from a finite action set $\mathcal A_{t,j}(s_j)$, collects the reward $r_{t,j}(s_j,a_j)\in\mathbb R$ and moves to $s_j'\in\mathcal S_{t+1,j}$ with probability $\mathbb P(s_j'\mid s_j,a_j)$; these probabilities are nonnegative and sum to one.
--
--   The components are coupled by $K$ **linking constraints** indexed by $\mathcal K=\{1,\dots,K\}$ with coefficients $C_{t,k,j}(s_j,a_j)\in\mathbb R$ and right-hand sides $b_k\in\mathbb R$. The WDP state is $s=(s_1,\dots,s_J)\in\mathcal S_t=\times_{j}\mathcal S_{t,j}$ and its action set is
--   $$\mathcal A_t(s)=\Big\{a\in\textstyle\times_{j}\mathcal A_{t,j}(s_j):\ \sum_{j\in\mathcal J}C_{t,k,j}(s_j,a_j)\le b_k\ \ \forall k\in\mathcal K\Big\}.$$
--   The WDP transition probability and reward are $\mathbb P(s'\mid s,a)=\prod_j\mathbb P(s_j'\mid s_j,a_j)$ and $r_t(s,a)=\sum_j r_{t,j}(s_j,a_j)$, and
--   $$\mathscr F_t=\{(s,a): s\in\mathcal S_t,\ a\in\mathcal A_t(s)\}$$
--   is the set of **feasible state–action pairs** of period $t$. The initial state space is the singleton $\mathcal S_0=\{s^0\}$, and $\mathcal A_t(s)\neq\emptyset$ for every decision period $t$ and every $s\in\mathcal S_t$.
--
--   This is the model on which every program and theorem of the mission is written.
--
--   **Formalization Note** Components, constraints and network layers are 0-based (`Fin J`, `Fin K`); periods are natural numbers with decision periods $t<T$. Action sets are `Finset`s of a finite action type. The coefficients $C$ and $b$ carry no sign restriction. The standing assumptions $\mathcal S_0=\{s^0\}$ (p.7), $\mathcal A_t(s)\ne\emptyset$ (a policy returns a feasible action, p.6) and the stochasticity of the component transitions are fields of the structure.
-- source:
--   S. Nadarajah, A. A. Cire, Self-Adapting Network Relaxations for Weakly Coupled Markov Decision Processes, SSRN 4081430 (version of Aug. 2023), https://ssrn.com/abstract=4081430, §2.1, pp.6–7 (WDP, $\mathcal A_t(s)$, $\mathbb P(s'|s,a)$, $r_t$, $\mathcal S_0=\{s^0\}$); §3.1, p.11 ($\mathscr F_t$)

import Mathlib

open scoped Classical

namespace SelfAdaptingFNR

/-- **Weakly coupled Markov decision process (WDP)** of Nadarajah & Cire, *Self-Adapting Network
Relaxations for Weakly Coupled Markov Decision Processes*, SSRN 4081430 (Aug. 2023), §2.1,
pp.6–7.

`J` component MDPs share the decision periods `t ∈ {0,…,T−1}` and the terminal period `T`.
In period `t` component `j` is in a state of the finite space `S t j`, applies an action from the
finite set `A t j s ⊆ Act t j`, collects the reward `r t j s a` and moves to `s' ∈ S (t+1) j`
with probability `P t j s a s'`. The `K` linking constraints read
`∑ⱼ C t k j (sⱼ) (aⱼ) ≤ b k`. The initial state space is the singleton `{s0}`, and every WDP
state of a decision period has a feasible action.

**Formalization Note.** Components are indexed by `Fin J` (the paper's `j` is the index `+ 1`),
constraints by `Fin K`, periods by `t : ℕ` (decision periods `t < T`, terminal period `T`; data
at `t > T` is never used). The action types `Act t j` are finite; the paper's finite action sets
are the `Finset`s `A t j s`, so this changes no instance. Transition probabilities are
nonnegative and sum to one over the next component state for every feasible component action
(p.6: "with probability `ℙ(s′ⱼ|sⱼ,aⱼ) ∈ [0,1]`"). `S0_singleton` is p.7's "we assume a singleton
initial state, that is, `𝒮₀ = {s⁰}`"; `A_nonempty` is the standing assumption that a policy
returns a feasible action `a ∈ 𝒜_t(s)` at every state of a decision period (p.6), without which
the maximum of the Bellman equations (1) is undefined. Coefficients `C` and right-hand sides `b`
have no sign restriction. -/
structure WDP (J K T : ℕ) where
  /-- Component state spaces `𝒮_{t,j}`. -/
  S : ℕ → Fin J → Type
  /-- Component action types; the feasible actions are `A t j s`. -/
  Act : ℕ → Fin J → Type
  instFintypeS : ∀ t j, Fintype (S t j)
  instFintypeAct : ∀ t j, Fintype (Act t j)
  /-- Component action sets `𝒜_{t,j}(sⱼ)`. -/
  A : (t : ℕ) → (j : Fin J) → S t j → Finset (Act t j)
  /-- Component transition probabilities `ℙ(s′ⱼ | sⱼ, aⱼ)` from period `t` to `t + 1`. -/
  P : (t : ℕ) → (j : Fin J) → S t j → Act t j → S (t + 1) j → ℝ
  /-- Component rewards `r_{t,j}(sⱼ, aⱼ)`. -/
  r : (t : ℕ) → (j : Fin J) → S t j → Act t j → ℝ
  /-- Linking-constraint coefficients `C_{t,k,j}(sⱼ, aⱼ)`. -/
  C : (t : ℕ) → Fin K → (j : Fin J) → S t j → Act t j → ℝ
  /-- Right-hand sides `b_k`. -/
  b : Fin K → ℝ
  /-- The initial state `s⁰ = (s⁰₁, …, s⁰_J)`. -/
  s0 : (j : Fin J) → S 0 j
  P_nonneg : ∀ t j (s : S t j) (a : Act t j) (s' : S (t + 1) j), a ∈ A t j s → 0 ≤ P t j s a s'
  P_sum_one : ∀ t j (s : S t j) (a : Act t j), a ∈ A t j s → ∑ s' : S (t + 1) j, P t j s a s' = 1
  /-- `𝒮₀ = {s⁰}`. -/
  S0_singleton : ∀ (j : Fin J) (s : S 0 j), s = s0 j
  /-- `𝒜_t(s) ≠ ∅` for every decision period `t` and every WDP state `s ∈ 𝒮_t`. -/
  A_nonempty : ∀ t, t < T → ∀ s : (j : Fin J) → S t j, ∃ a : (j : Fin J) → Act t j,
    (∀ j, a j ∈ A t j (s j)) ∧ ∀ k, ∑ j, C t k j (s j) (a j) ≤ b k

attribute [instance] WDP.instFintypeS WDP.instFintypeAct

variable {J K T : ℕ}

/-- The WDP action set `𝒜_t(s)` (p.6): component-feasible action vectors satisfying the `K`
linking constraints. -/
noncomputable def WDP.actionSet (M : WDP J K T) (t : ℕ) (s : (j : Fin J) → M.S t j) :
    Finset ((j : Fin J) → M.Act t j) :=
  (Fintype.piFinset fun j => M.A t j (s j)).filter
    fun a => ∀ k, ∑ j, M.C t k j (s j) (a j) ≤ M.b k

/-- The set `𝓕_t := {(s, a) : s ∈ 𝒮_t, a ∈ 𝒜_t(s)}` of feasible state–action pairs (p.11). -/
def WDP.feasiblePairs (M : WDP J K T) (t : ℕ) :
    Set (((j : Fin J) → M.S t j) × ((j : Fin J) → M.Act t j)) :=
  {p | (∀ j, p.2 j ∈ M.A t j (p.1 j)) ∧ ∀ k, ∑ j, M.C t k j (p.1 j) (p.2 j) ≤ M.b k}

/-- The WDP transition probability `ℙ(s′|s,a) := ∏ⱼ ℙ(s′ⱼ|sⱼ,aⱼ)` (p.6). -/
noncomputable def WDP.transProb (M : WDP J K T) (t : ℕ) (s : (j : Fin J) → M.S t j)
    (a : (j : Fin J) → M.Act t j) (s' : (j : Fin J) → M.S (t + 1) j) : ℝ :=
  ∏ j, M.P t j (s j) (a j) (s' j)

/-- The WDP reward `r_t(s,a) := ∑ⱼ r_{t,j}(sⱼ,aⱼ)` (p.6). -/
noncomputable def WDP.reward (M : WDP J K T) (t : ℕ) (s : (j : Fin J) → M.S t j)
    (a : (j : Fin J) → M.Act t j) : ℝ :=
  ∑ j, M.r t j (s j) (a j)

theorem WDP.mem_actionSet (M : WDP J K T) (t : ℕ) (s : (j : Fin J) → M.S t j)
    (a : (j : Fin J) → M.Act t j) :
    a ∈ M.actionSet t s ↔ (s, a) ∈ M.feasiblePairs t := by
  simp [WDP.actionSet, WDP.feasiblePairs, Fintype.mem_piFinset]

theorem WDP.actionSet_nonempty (M : WDP J K T) {t : ℕ} (ht : t < T)
    (s : (j : Fin J) → M.S t j) : (M.actionSet t s).Nonempty := by
  obtain ⟨a, ha⟩ := M.A_nonempty t ht s
  exact ⟨a, (M.mem_actionSet t s a).2 ha⟩

end SelfAdaptingFNR


