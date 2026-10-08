-- Prove2me | Definitions.Def_FoundationsRL_RLBasics_UCBVI_v2
-- name    : FoundationsRL_RLBasics_UCBVI_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:16:42.097472+00:00
-- url     : https://prove2.me/theorems/e220538d-b09c-4e84-bf4e-b56b13b328ca
-- title:
--   The UCB-VI algorithm and its regret, as a finite process over T episodes (v2: optimistic value 1 for unvisited pairs)
-- statement:
--   Corrected re-issue of `FoundationsRL_RLBasics_UCBVI` with the same namespace and declaration names (`Trajectory`, `Learner`, `trajProb`, `historyProb`, `probEvent`, `countSA`, `countSAS`, `estExp`, `bonus`, `ucbQ`, `ucbGreedy`, `ucbviLearner`, `regret`), formalizing the UCB-VI algorithm of §5.6 (p. 89) and the online-RL regret of Eq. (5.3) under Assumption 6, with the $T$-episode interaction modeled as a finite probability space (finite sums over the finite type of $T$-episode outcomes).
--
--   The only change is in `ucbQ`, the value estimates $Q^t_h$ of Eq. (5.26): $Q^t_h(s,a)=\{r_h(s,a)+\mathbb E_{s'\sim\hat P^t_h(\cdot|s,a)}[\bar V^t_{h+1}(s')]+b^t_{h,\delta}(s,a)\}\wedge 1$ with $\bar V^t_{h+1}(s')=\max_a Q^t_{h+1}(s',a)$ and $Q^t_{H+1}\equiv 0$. For an unvisited pair, $n^t_h(s,a)=0$, the book's bonus $b^t_{h,\delta}(s,a)=2\sqrt{\log(2SAHT/\delta)/n^t_h(s,a)}$ (Eq. (5.27)) is $+\infty$, so the clipping gives $Q^t_h(s,a)=1$; `ucbQ` now implements this case explicitly. The retired version evaluated the bonus formula at $n=0$ through Lean's convention $x/0=0$, giving bonus $0$ and the non-optimistic value $r_h(s,a)\wedge 1$, so the formalized learner could lock onto a myopic action and never explore (which is not UCB-VI). `bonus` is unchanged and is only used for $n\ge 1$. The algorithm box prints $\bar V^t_{H+1}\equiv 1$ while the analysis (Eq. (5.29), Lemma 16) uses $Q_{H+1}\equiv 0$; the formalization follows the analysis.
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

**Version 2** (corrected replacement of `Def_FoundationsRL_RLBasics_UCBVI`, same namespace
and declaration names). The retired version evaluated the bonus `2√(log(2SAHT/δ)/n)` of
Eq. (5.27) at `n = n^t_h(s,a) = 0` through Lean's convention `x / 0 = 0`, so an unvisited
state-action pair received the bonus `0` (and `estExp = 0`), i.e. the non-optimistic value
`Q^t_h(s,a) = r_h(s,a) ∧ 1`; the resulting learner could lock onto a myopic action and never
explore, which is not UCB-VI. In the book the bonus at `n = 0` is `+∞`, so the clipping `∧ 1`
in Eq. (5.26) makes `Q^t_h(s,a) = 1` (maximally optimistic) for every unvisited pair. `ucbQ`
below implements exactly this case split; `bonus` itself is unchanged and is only ever used
for `n ≥ 1`. The book's algorithm box prints `V̄^t_{H+1} ≡ 1`, while its analysis (Eq. (5.29),
Lemma 16) uses `Q_{H+1} ≡ 0`; we follow the analysis (`ucbQ _ _ _ _ _ H = 0`).
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

/-- The UCB-VI bonus `b^t_{h,δ}(s,a) = 2√(log(2SAHT/δ)/n^t_h(s,a))` (Eq. (5.27)), for
`n = n^t_h(s,a) ≥ 1`. At `n = 0` the book's formula is `+∞`; that case is handled explicitly
in `ucbQ` (an unvisited pair gets the clipped value `1`), never through this function. -/
noncomputable def bonus (δ : ℝ) (Scard Acard H T n : ℕ) : ℝ :=
  2 * Real.sqrt (Real.log (2 * Scard * Acard * H * T / δ) / n)

/-- The UCB-VI value estimates `Q^t_h` (Eq. (5.26)), given known mean rewards `r`, computed
by backward induction over the history `hist` of past episodes:
`Q^t_h(s,a) = {r_h(s,a) + E_{s'∼P̂^t_h(·∣s,a)}[V̄^t_{h+1}(s')] + b^t_{h,δ}(s,a)} ∧ 1` with
`V̄^t_{h+1}(s') = max_a Q^t_{h+1}(s',a)` and `Q^t_{H+1} ≡ 0`. For an unvisited pair
(`n^t_h(s,a) = 0`) the book's bonus (5.27) is `+∞`, so the clipped value is `1`; this is the
first branch below. -/
noncomputable def ucbQ (M : EpisodicMDP S A H) (r : ℕ → S → A → ℝ) (δ : ℝ) (T : ℕ)
    (hist : List (Trajectory S A H)) : ℕ → S → A → ℝ
  | h, s, a =>
      if hh : h < H then
        if countSA hist h s a = 0 then 1 else
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


