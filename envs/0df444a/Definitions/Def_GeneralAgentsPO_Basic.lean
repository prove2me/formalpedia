-- Prove2me | Definitions.Def_GeneralAgentsPO_Basic
-- name    : GeneralAgentsPO_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T05:17:10.583349+00:00
-- url     : https://prove2.me/theorems/d18c6e6a-7142-4042-9905-05962831580a
-- title:
--   Stochastic and observation-based goal-conditioned policies, success probabilities and $\delta$-optimality
-- statement:
--   Objects of Sections 2 and 4 of Cifuentes (2026). The framework of Section 2 is that of Richens et al. (2025); its cMDP, goals and goal semantics are imported from the definitions file `GeneralAgentsWorldModels_Basic`.
--
--   1. **cMDP (Definition 1, imported).** Finite sets $\mathcal S$ of states and $\mathcal A$ of actions and a kernel $P(s'\mid s,a)\ge0$ with $\sum_{s'}P(s'\mid s,a)=1$. It is communicating if the directed graph with an edge $s\to s'$ whenever $P(s'\mid s,a)>0$ for some $a$ is strongly connected.
--   2. **Goals (Definition 2, imported).** A basic goal is $\top[V]$, $\bigcirc[V]$ or $\Diamond[V]$ with $V\subseteq\mathcal S\times\mathcal A$; a sequential goal is a finite list $\langle\varphi_1,\dots,\varphi_n\rangle$ of basic goals; a goal is a finite disjunction $\bigvee_{i\in I}\psi_i$ of sequential goals. A history $h=s_0a_0s_1a_1\dots$ satisfies $\langle\top[V],\dots\rangle$ if $(s_0,a_0)\in V$ and $h$ satisfies the rest; $\langle\bigcirc[V],\dots\rangle$ if $(s_1,a_1)\in V$ and $s_1a_1\dots$ satisfies the rest; $\langle\Diamond[V],\dots\rangle$ if there is a least $i$ with $(s_i,a_i)\in V$ and $s_ia_i\dots$ satisfies the rest.
--   3. **Depth and width.** $\mathrm{depth}(\bigvee_i\psi_i)=\max_i\mathrm{length}(\psi_i)$ and $\mathrm{width}(\bigvee_{i\in I}\psi_i)=|I|$. $\Psi_n$ is the set of goals of depth $n$, and $\Psi_{n,k}$ the set of goals of depth $n$ and width $k$. Two goals are incompatible if no history satisfies both.
--   4. **The goals of Section 3.** For $b\in\mathcal A$ and $w\in\{0,1\}^n$, $\varphi_{b,w}=\langle\top[A=b],\varphi_2,\varphi_3^{w_1},\dots,\varphi_2,\varphi_3^{w_n}\rangle$ with $\varphi_2=\Diamond[S=s,A=a]$, $\varphi_3^1=\bigcirc[S=s']$, $\varphi_3^0=\bigcirc[S\neq s']$; $\varphi_w$ is the same goal without the leading $\top[A=b]$; $|w|_1$ is the number of ones of $w$. $\rho_{b,r}=\bigvee_{|w|_1=r}\varphi_{b,w}$ (eq. (1)), $\psi_{b,k}=\bigvee_{r\le k}\rho_{b,r}$ and $\chi_{b,k}=\bigvee_{r>k}\rho_{b,r}$ (eq. (3)). $\mathrm{Bin}_n(p)(r)=\binom nr p^r(1-p)^{n-r}$.
--   5. **Policies.** A policy maps each finite history $x_0a_0\dots x_t$ to a probability distribution on $\mathcal A$; it is deterministic if each of these distributions is a point mass. A goal-conditioned policy is a family $(\pi_\psi)_{\psi\in\Psi}$ of policies. In a cMDP the histories are over states; for an observation-based policy they are over observations.
--   6. **Success probability.** For a policy $\pi$ and a start state $s$, the probability of the cylinder of histories beginning with $(s_0,a_0),\dots,(s_{T-1},a_{T-1})$ is $[s_0=s]\prod_{i<T}\Pr(\pi(s_0a_0\dots s_i)=a_i)\prod_{i+1<T}P(s_{i+1}\mid s_i,a_i)$, and $\Pr(\psi\mid\pi,s)$ is the probability of the set of histories satisfying $\psi$.
--   7. **$\delta$-optimality (Definition 3).** $\pi$ is $\delta$-optimal for $\Phi\subseteq\Psi$ if $(1-\delta)\sup_{\pi'}\Pr(\varphi\mid\pi',s)\le\Pr(\varphi\mid\pi_\varphi,s)$ for all $\varphi\in\Phi$ and all $s\in\mathcal S$, the supremum being over all policies.
--   8. **Partial observability (Definition 4, Section 4.2).** A partially observable cMDP adds a finite set $O$ of observations and a kernel $\Omega(o\mid s)$. For an observation-based policy $\pi$, the probability of the cylinder of state histories beginning with $(s_i,a_i)_{i<T}$ is $\sum_{o_0,\dots,o_{T-1}}[s_0=s]\prod_{i<T}\Omega(o_i\mid s_i)\Pr(\pi(o_0a_0\dots o_i)=a_i)\prod_{i+1<T}P(s_{i+1}\mid s_i,a_i)$. Success probabilities, optimal values and $\delta$-optimality are defined from it as in items 6 and 7, with the supremum over observation-based policies. Goals are still phrased in terms of states.
--
--   **Formalization Note** Every goal is satisfied, if at all, at a finite time, so the event that a history satisfies $\psi$ is the increasing union over $T$ of the events that its first $T$ pairs already force $\psi$. $\Pr(\psi\mid\pi,s)$ is therefore defined as the supremum over $T$ of the (finite) probabilities of these events, which is the value of the cylinder-set measure on histories. The maximum $\max_\pi$ of the paper is written as a supremum. The paper does not say whether $O$ is finite; here it is.
-- source:
--   Cifuentes, General Agents Contain World Models, even under Partial Observability and Stochasticity, arXiv:2602.03146v1 (2026), Section 2 (Definitions 1-3, pp. 2-5), Section 4.2 (Definition 4, pp. 11-12), Section 4.3 (width, p. 15)

import Mathlib
import Definitions.Def_GeneralAgentsWorldModels_Basic

/-!
Cifuentes, *General Agents Contain World Models, even under Partial Observability and
Stochasticity*, arXiv:2602.03146v1 (2026).

Section 2 of the paper restates the framework of Richens et al. (arXiv:2506.01622). The
controlled Markov decision process (Definition 1, `CMP`), the communicating condition
(`CMP.IsCommunicating`), basic, sequential and general goals with their semantics (Definition 2,
`SubGoal`, `SeqGoal`, `CompGoal`, `seqSat`, `compSat`), the finite-prefix test `Decides`, the goals
`φ_{b,w}` and `ρ_{b,r}` of eq. (1) (`trialSeq`, `binGoal`) and the binomial mass function
(`binPmf`) are reused from `Definitions.Def_GeneralAgentsWorldModels_Basic`.

This file adds what is new in the paper: depth and width of goals and the classes `Ψ_n`,
`Ψ_{n,k}` (Sections 2 and 4.3), stochastic history-dependent policies and goal-conditioned
policies (Section 2), the probability that a stochastic policy achieves a goal (Section 2),
`δ`-optimality (Definition 3), partially observable cMDPs (Definition 4), observation-based
policies and the probability that they achieve a goal (Section 4.2).
-/

noncomputable section

open GeneralAgentsWorldModels

namespace GeneralAgentsPO

/-- Section 2 (p. 4): the depth of a goal `⋁_{i ∈ I} ψ_i`, the length of its longest sequential
goal, `depth(⋁_i ψ_i) = max_i depth(ψ_i)`, `depth(⟨φ₁, …, φ_n⟩) = n` (the empty disjunction has
depth `0`). -/
def goalDepth {S A : Type*} (ψ : CompGoal S A) : ℕ := (ψ.map List.length).foldr max 0

/-- Section 4.3 (p. 15): the width of a goal `⋁_{i ∈ I} ψ_i`, the number `|I|` of its
disjuncts. -/
def goalWidth {S A : Type*} (ψ : CompGoal S A) : ℕ := ψ.length

/-- Section 2 (p. 4): `Ψ_n`, the set of goals of depth `n`. -/
def PsiDepth {S A : Type*} (n : ℕ) : Set (CompGoal S A) := {ψ | goalDepth ψ = n}

/-- Section 4.3 (p. 15): `Ψ_{n,k}`, the set of goals of depth `n` and width `k`. -/
def PsiDepthWidth {S A : Type*} (n k : ℕ) : Set (CompGoal S A) :=
  {ψ | goalDepth ψ = n ∧ goalWidth ψ = k}

/-- Section 2 (p. 5): two goals are incompatible if no history satisfies both. -/
def IsIncompatible {S A : Type*} (φ₁ φ₂ : CompGoal S A) : Prop :=
  ∀ τ : ℕ → S × A, compSat φ₁ τ → ¬ compSat φ₂ τ

/-- Section 2 (p. 5), the sequential goal `φ_w = ⟨φ₂, φ₃^{w₁}, …, φ₂, φ₃^{w_n}⟩` of the proof of
Theorem 3 (p. 13), with `φ₂ = ◇[S = s, A = a]`, `φ₃^1 = ◯[S = s']`, `φ₃^0 = ◯[S ≠ s']`. The goal
`φ_{b,w}` of Section 3 is `trialSeq b s a s' w = ⊤[A = b] :: visitSeq s a s' w`. -/
def visitSeq {S A : Type*} (s : S) (a : A) (s' : S) (w : List Bool) : SeqGoal S A :=
  w.flatMap fun c => [evVisit s a, nextIn (if c then {s'} else {s'}ᶜ)]

/-- Section 3 (p. 6): `|w|_1 = |{i : w_i = 1}|` for `w ∈ {0,1}^n`. -/
def onesCount {n : ℕ} (w : Fin n → Bool) : ℕ := (Finset.univ.filter fun i => w i = true).card

/-- Section 2 (p. 4): a (stochastic, history-dependent) policy `π : H_F → Δ(A)`. A finite history
`x₀ a₀ … x_{t-1} a_{t-1} x_t` is given by the list of its past pairs `(x_i, a_i)`, `i < t`, and its
last element `x_t`; `act h x c` is `Pr(π(h x) = c)`. With `X = S` this is a policy of a cMDP; with
`X = O` it is an observation-based policy (Section 4.2, p. 11). -/
structure StochPolicy (X A : Type*) [Fintype A] where
  /-- `act h x c = Pr(π(h x) = c)`. -/
  act : List (X × A) → X → A → ℝ
  nonneg : ∀ h x c, 0 ≤ act h x c
  sum_one : ∀ h x, ∑ c, act h x c = 1

/-- Section 2 (p. 4): a policy is deterministic if for every finite history some action has
probability `1`. -/
def StochPolicy.IsDeterministic {X A : Type*} [Fintype A] (π : StochPolicy X A) : Prop :=
  ∀ h x, ∃ c, π.act h x c = 1

/-- Section 2 (p. 4): a goal-conditioned policy `π : H_F × Ψ → Δ(A)`, written `ψ ↦ π_ψ`; goals are
over `S × A`, and the policy reads histories over `X` (`X = S`, or `X = O` for an observation-based
policy, Section 4.2). -/
abbrev GCStochPolicy (S X A : Type*) [Fintype A] := CompGoal S A → StochPolicy X A

/-- The list of the first `i` entries `u 0, …, u (i-1)` of a finite sequence `u`. -/
def histBefore {X : Type*} {T : ℕ} (u : Fin T → X) (i : Fin T) : List X :=
  List.ofFn fun j : Fin i.val => u (Fin.castLE i.isLt.le j)

open Classical in
/-- Section 2 (p. 4): the probability, under the policy `π` started at `s`, of the cylinder set of
histories whose first `T` state-action pairs are `u = ((s₀, a₀), …, (s_{T-1}, a_{T-1}))`:
`[s₀ = s] ∏_{i<T} Pr(π(h_i) = a_i) ∏_{i+1<T} P(s_{i+1} | s_i, a_i)`, `h_i = s₀ a₀ … s_i`. -/
def prefixProb {S A : Type*} [Fintype S] [Fintype A] (M : CMP S A) (π : StochPolicy S A) (s : S)
    {T : ℕ} (u : Fin T → S × A) : ℝ :=
  (if ∀ h : 0 < T, (u ⟨0, h⟩).1 = s then 1 else 0) *
    ∏ i : Fin T, (π.act (histBefore u i) (u i).1 (u i).2 *
      if h : i.val + 1 < T then M.P (u i).1 (u i).2 (u ⟨i.val + 1, h⟩).1 else 1)

open Classical in
/-- The probability that the first `T` state-action pairs of the history generated by `π` from `s`
already guarantee `ψ` (every history with this prefix satisfies `ψ`). -/
def probUpTo {S A : Type*} [Fintype S] [Fintype A] (M : CMP S A) (π : StochPolicy S A)
    (ψ : CompGoal S A) (s : S) (T : ℕ) : ℝ :=
  ∑ u : Fin T → S × A, if Decides ψ (List.ofFn u) then prefixProb M π s u else 0

/-- Section 2 (p. 5): `Pr(ψ | π, s) = ∑_{h ⊨ ψ} Pr(h | π, s)`, the probability under the measure on
histories induced by `π` from `s` (extended from finite histories via cylinder sets) that the
history satisfies `ψ`. Satisfaction of a goal is decided by a finite prefix (p. 14), so the event
`h ⊨ ψ` is the increasing union over `T` of the events decided by the first `T` pairs, and its
probability is the supremum of their probabilities. -/
def goalProb {S A : Type*} [Fintype S] [Fintype A] (M : CMP S A) (π : StochPolicy S A)
    (ψ : CompGoal S A) (s : S) : ℝ :=
  ⨆ T : ℕ, probUpTo M π ψ s T

/-- Definition 3 (p. 5): `max_π Pr(ψ | π, s)`, the supremum over all (stochastic,
history-dependent) policies. -/
def optValue {S A : Type*} [Fintype S] [Fintype A] (M : CMP S A) (ψ : CompGoal S A) (s : S) : ℝ :=
  ⨆ π : StochPolicy S A, goalProb M π ψ s

/-- Definition 3 (p. 5): the goal-conditioned policy `π` is `δ`-optimal for `Φ ⊆ Ψ`: for all
`φ ∈ Φ` and `s ∈ S`, `(1 - δ) max_π' Pr(φ | π', s) ≤ Pr(φ | π_φ, s)`. It is `n`-th-degree
`δ`-optimal if it is `δ`-optimal for `Ψ_n`. -/
def IsDeltaOptimal {S A : Type*} [Fintype S] [Fintype A] (M : CMP S A) (δ : ℝ)
    (Φ : Set (CompGoal S A)) (π : GCStochPolicy S S A) : Prop :=
  ∀ φ ∈ Φ, ∀ s : S, (1 - δ) * optValue M φ s ≤ goalProb M (π φ) φ s

/-- Definition 4 (p. 11): a partially observable cMDP `(S, A, P, O, Ω)`: a cMDP `(S, A, P)`, a set
of observations `O` (here finite) and an observation kernel `obs s o = Ω(o | s)` with
`∑_o Ω(o | s) = 1`. -/
structure POCMP (S A O : Type*) [Fintype S] [Fintype O] extends CMP S A where
  /-- `obs s o = Ω(o | s)`. -/
  obs : S → O → ℝ
  obs_nonneg : ∀ s o, 0 ≤ obs s o
  obs_sum_one : ∀ s, ∑ o, obs s o = 1

open Classical in
/-- Section 4.2 (p. 12): the probability, under the observation-based policy `π` started at `s`,
that the first `T` state-action pairs are `u = ((s₀, a₀), …, (s_{T-1}, a_{T-1}))`:
`∑_{o₀ … o_{T-1}} [s₀ = s] ∏_{i<T} Ω(o_i | s_i) Pr(π(o₀ a₀ … o_i) = a_i) ∏_{i+1<T} P(s_{i+1} | s_i, a_i)`,
the joint probability of the state history and the observation history, summed over the
observations. -/
def obsPrefixProb {S A O : Type*} [Fintype S] [Fintype A] [Fintype O] (M : POCMP S A O)
    (π : StochPolicy O A) (s : S) {T : ℕ} (u : Fin T → S × A) : ℝ :=
  (if ∀ h : 0 < T, (u ⟨0, h⟩).1 = s then 1 else 0) *
    ∑ o : Fin T → O, ∏ i : Fin T, (M.obs (u i).1 (o i) *
      π.act (histBefore (fun j => (o j, (u j).2)) i) (o i) (u i).2 *
      if h : i.val + 1 < T then M.P (u i).1 (u i).2 (u ⟨i.val + 1, h⟩).1 else 1)

open Classical in
/-- The probability that the first `T` state-action pairs generated by the observation-based policy
`π` from `s` already guarantee `ψ`. -/
def obsProbUpTo {S A O : Type*} [Fintype S] [Fintype A] [Fintype O] (M : POCMP S A O)
    (π : StochPolicy O A) (ψ : CompGoal S A) (s : S) (T : ℕ) : ℝ :=
  ∑ u : Fin T → S × A, if Decides ψ (List.ofFn u) then obsPrefixProb M π s u else 0

/-- Section 4.2 (p. 12): `Pr(ψ | π, s) = ∑_{h ⊨ ψ} Pr(h | π, s)` for an observation-based policy;
goals are phrased in terms of the real states. As for `goalProb`, it is the supremum over `T` of
the probability that the first `T` pairs decide `ψ`. -/
def obsGoalProb {S A O : Type*} [Fintype S] [Fintype A] [Fintype O] (M : POCMP S A O)
    (π : StochPolicy O A) (ψ : CompGoal S A) (s : S) : ℝ :=
  ⨆ T : ℕ, obsProbUpTo M π ψ s T

/-- Section 4.2 (p. 12): `max_π Pr(ψ | π, s)` over observation-based policies. -/
def obsOptValue {S A O : Type*} [Fintype S] [Fintype A] [Fintype O] (M : POCMP S A O)
    (ψ : CompGoal S A) (s : S) : ℝ :=
  ⨆ π : StochPolicy O A, obsGoalProb M π ψ s

/-- Definition 3 read in a partially observable cMDP (Section 4.2, p. 12): the goal-conditioned
observation-based policy `π` is `δ`-optimal for `Φ`. -/
def IsObsDeltaOptimal {S A O : Type*} [Fintype S] [Fintype A] [Fintype O] (M : POCMP S A O)
    (δ : ℝ) (Φ : Set (CompGoal S A)) (π : GCStochPolicy S O A) : Prop :=
  ∀ φ ∈ Φ, ∀ s : S, (1 - δ) * obsOptValue M φ s ≤ obsGoalProb M (π φ) φ s

end GeneralAgentsPO


