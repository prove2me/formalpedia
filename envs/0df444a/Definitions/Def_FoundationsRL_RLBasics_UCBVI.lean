-- Prove2me | Definitions.Def_FoundationsRL_RLBasics_UCBVI
-- name    : FoundationsRL_RLBasics_UCBVI
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T05:01:47.665473+00:00
-- url     : https://prove2.me/theorems/b48796a5-b871-49fe-ac3d-924a82ede334
-- title:
--   The UCB-VI algorithm and its regret, as a finite process over T episodes
-- statement:
--   This file formalizes the UCB-VI algorithm of §5.6 (p. 89) and the online-RL regret of Eq. (5.3), under Assumption 6 (rewards deterministic, known, and bounded in $[0,1]$; $V^{M,\star}_1 \in [0,1]$).
--
--   A `Trajectory S A H` is one realized episode: a pair `(s0, f)` where `f : Fin H → A × S` records, at each layer, the action taken and the resulting next state. Since $S$, $A$ and $H$ are all finite, `Trajectory S A H` is itself a finite type, and a `Learner` is a function from the list of previously realized episode trajectories to the policy played in the next episode (a history-dependent algorithm). `trajProb M π τ` is the probability that trajectory $\tau$ is realized under $(M,\pi)$; `historyProb M learner histT` is the probability of realizing all $T$ episodes as `histT`, as the finite product, over episodes $t$, of the probability of episode $t$'s trajectory under the policy `learner` plays given the first $t$ trajectories of `histT` — i.e. the joint law of the adaptive, $T$-episode interaction protocol of the book's "Online RL" paragraph (p. 82). Because the outcome space `Fin T → Trajectory S A H` is finite, `probEvent` (the probability of an event on the $T$-episode outcome) is a plain finite sum — no measure theory is used anywhere in this mission.
--
--   `countSA`/`countSAS` are the empirical counts $n^t_h(s,a)$, $n^t_h(s,a,s')$ of Eq. (5.25) read off a list of past trajectories; `estExp` is the corresponding empirical-transition expectation $\mathbb E_{s'\sim\widehat P^t_h(\cdot\mid s,a)}[f(s')]$ (by convention $0$ when $n^t_h(s,a)=0$). `bonus δ S A H T n` is the explicit UCB-VI bonus $b_{h,\delta}(s,a) = 2\sqrt{\log(2SAHT/\delta)/n}$ of Eq. (5.27). `ucbQ` is the value estimate $Q^t_h$ of Eq. (5.26), computed by backward induction over the layer from a given history of past episodes; `ucbGreedy`/`ucbviLearner` package the greedy policy $\widehat\pi^t$ and the resulting learner. `regret M r δ T histT` is $\mathrm{Reg} = \sum_{t=1}^T \big(f^M(\pi^{M,\star}) - f^M(\pi^t)\big)$ of Eq. (5.3), as a function of the realized $T$-episode history (round $t$'s policy `ucbviLearner M r δ T` depends only on the history's first $t$ trajectories, matching the book's protocol that $\pi^t$ is chosen before episode $t$'s trajectory is observed).
--
--   **Formalization Note** `ucbQ`'s recursion is well-founded on $H-h$ (increasing $h$ toward the terminal layer $H$, where it returns $0$, matching $Q_{H+1}\equiv 0$). `countSA`/`countSAS`/`estExp`/`bonus` are marked `noncomputable` only because they are built from `actionAt`, whose out-of-range branch (`h \ge H`, never exercised in this mission) uses `Classical.arbitrary`.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 82, 89–90, §5.6 and Eqs. (5.3), (5.25)–(5.27)

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core

open scoped Classical

/-!
The UCB-VI algorithm (Foster & Rakhlin, §5.6, p. 89) for tabular episodic RL: `T` episodes
of interaction with an unknown MDP `M`, under Assumption 6 (rewards deterministic, bounded,
known). A `Trajectory` fixes one episode's realized `(s_0, a_0, s_1), …, (a_{H-1}, s_H)`; the
process over `T` episodes is built as a finite product (over the finite type of joint
`T`-episode outcomes) of the per-episode transition probabilities induced by a
history-dependent `Learner`, so "probability" and "expectation" below are plain finite sums —
no measure theory is needed since `S`, `A`, `H`, `T` are all finite.
-/

namespace FoundationsRL.RLBasics

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
  {H : ℕ}

/-- One episode's realized trajectory: an initial state and, for each layer `< H`, the
action taken and the resulting next state. -/
abbrev Trajectory (S A : Type*) (H : ℕ) := S × (Fin H → A × S)

/-- A history-dependent learner: the policy played in an episode, as a function of the list
of previously-realized episode trajectories. -/
def Learner (S A : Type*) (H : ℕ) := List (Trajectory S A H) → Policy S A H

/-- The action recorded at layer `h` of `τ` (junk `Classical.arbitrary A` if `h ≥ H`, never
queried in that range below). -/
noncomputable def actionAt (τ : Trajectory S A H) (h : ℕ) : A :=
  if hh : h < H then (τ.2 ⟨h, hh⟩).1 else Classical.arbitrary A

/-- The state reached at the end of layer `h` of `τ` (i.e. the book's `s_{h+1}`); junk `τ.1`
if `h ≥ H`, never queried in that range below. -/
def nextStateAt (τ : Trajectory S A H) (h : ℕ) : S :=
  if hh : h < H then (τ.2 ⟨h, hh⟩).2 else τ.1

/-- The state at layer `h` of `τ` (`stateAt τ 0 = τ.1`, `stateAt τ (h+1) = nextStateAt τ h`). -/
def stateAt (τ : Trajectory S A H) : ℕ → S
  | 0 => τ.1
  | h + 1 => nextStateAt τ h

/-- The probability, under MDP `M` and policy `π`, that episode trajectory `τ` occurs. -/
noncomputable def trajProb (M : EpisodicMDP S A H) (π : Policy S A H) (τ : Trajectory S A H) :
    ℝ :=
  M.d1 τ.1 * ∏ h : Fin H, π h.1 (stateAt τ h.1) (actionAt τ h.1) *
    M.P h.1 (stateAt τ h.1) (actionAt τ h.1) (nextStateAt τ h.1)

/-- The probability, under MDP `M` and history-dependent `learner`, that the `T` episodes
realize exactly `histT`. -/
noncomputable def historyProb (M : EpisodicMDP S A H) (learner : Learner S A H) {T : ℕ}
    (histT : Fin T → Trajectory S A H) : ℝ :=
  ∏ t : Fin T, trajProb M (learner ((List.ofFn histT).take t.1)) (histT t)

/-- The probability of an event on the `T`-episode outcome, under MDP `M` and `learner`. -/
noncomputable def probEvent (M : EpisodicMDP S A H) (learner : Learner S A H) (T : ℕ)
    (E : (Fin T → Trajectory S A H) → Prop) : ℝ :=
  ∑ histT : Fin T → Trajectory S A H, if E histT then historyProb M learner histT else 0

/-- `n^t_h(s,a)` (Eq. (5.25)): the number of past episodes, among `hist`, whose layer-`h`
state-action pair is `(s,a)`. -/
noncomputable def countSA (hist : List (Trajectory S A H)) (h : ℕ) (s : S) (a : A) : ℕ :=
  (hist.filter (fun τ => decide (stateAt τ h = s ∧ actionAt τ h = a))).length

/-- `n^t_h(s,a,s')` (Eq. (5.25)). -/
noncomputable def countSAS (hist : List (Trajectory S A H)) (h : ℕ) (s : S) (a : A) (s' : S) :
    ℕ :=
  (hist.filter (fun τ =>
    decide (stateAt τ h = s ∧ actionAt τ h = a ∧ nextStateAt τ h = s'))).length

/-- The estimated-transition expectation `E_{s' ∼ P̂^t_h(·∣s,a)}[f(s')]` of Eq. (5.25)
(convention: `0` when `n^t_h(s,a) = 0`, i.e. no data has been collected). -/
noncomputable def estExp (hist : List (Trajectory S A H)) (h : ℕ) (s : S) (a : A)
    (f : S → ℝ) : ℝ :=
  let n := countSA hist h s a
  if n = 0 then 0 else (∑ s' : S, (countSAS hist h s a s' : ℝ) * f s') / (n : ℝ)

/-- The UCB-VI bonus `b^t_{h,δ}(s,a) = 2√(log(2SAHT/δ)/n^t_h(s,a))` (Eq. (5.27)). -/
noncomputable def bonus (δ : ℝ) (Scard Acard H T n : ℕ) : ℝ :=
  2 * Real.sqrt (Real.log (2 * Scard * Acard * H * T / δ) / n)

/-- The UCB-VI value estimates `Q^t_h` (Eq. (5.26)), given known mean rewards `r`, computed
by backward induction over the history `hist` of past episodes. -/
noncomputable def ucbQ (M : EpisodicMDP S A H) (r : ℕ → S → A → ℝ) (δ : ℝ) (T : ℕ)
    (hist : List (Trajectory S A H)) : ℕ → S → A → ℝ
  | h, s, a =>
      if hh : h < H then
        min 1 (r h s a
          + estExp hist h s a (fun s' => ⨆ a' : A, ucbQ M r δ T hist (h + 1) s' a')
          + bonus δ (Fintype.card S) (Fintype.card A) H T (countSA hist h s a))
      else 0
  termination_by h => H - h
  decreasing_by all_goals omega

/-- The greedy action `arg max_a Q^t_h(s,a)` w.r.t. `ucbQ`. -/
noncomputable def ucbGreedy (M : EpisodicMDP S A H) (r : ℕ → S → A → ℝ) (δ : ℝ) (T : ℕ)
    (hist : List (Trajectory S A H)) (h : ℕ) (s : S) : A :=
  ((Finset.univ : Finset A).toList.argmax (ucbQ M r δ T hist h s)).getD (Classical.arbitrary A)

/-- The UCB-VI learner: at every episode, play the deterministic policy greedy w.r.t.
`ucbQ` computed from the episodes collected so far. -/
noncomputable def ucbviLearner (M : EpisodicMDP S A H) (r : ℕ → S → A → ℝ) (δ : ℝ) (T : ℕ) :
    Learner S A H :=
  fun hist => detPolicy (ucbGreedy M r δ T hist)

/-- The regret (Eq. (5.3)) of UCB-VI over `T` episodes, as a function of the realized
`T`-episode history `histT` (round `t`'s policy depends only on the first `t` trajectories
of `histT`). -/
noncomputable def regret (M : EpisodicMDP S A H) (r : ℕ → S → A → ℝ) (δ : ℝ) (T : ℕ)
    (histT : Fin T → Trajectory S A H) : ℝ :=
  ∑ t : Fin T,
    ((∑ s : S, M.d1 s * Vstar M 0 s) -
      ∑ s : S, M.d1 s * V M (ucbviLearner M r δ T ((List.ofFn histT).take t.1)) 0 s)

end FoundationsRL.RLBasics


