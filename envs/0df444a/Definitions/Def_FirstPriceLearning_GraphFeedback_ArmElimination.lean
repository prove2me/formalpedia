-- Prove2me | Definitions.Def_FirstPriceLearning_GraphFeedback_ArmElimination
-- name    : FirstPriceLearning_GraphFeedback_ArmElimination
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:52.58499+00:00
-- url     : https://prove2.me/theorems/711313cb-51bc-4a64-b02b-fd13b63dd131
-- title:
--   Algorithms 1 and 2: arm elimination with graph feedback and cross learning
-- statement:
--   This module defines Algorithm 2 of Han, Zhou and Weissman (p. 15), arm elimination for stochastic contextual bandits with graph feedback and cross learning, and Algorithm 1 (p. 12) as its case with a single context.
--
--   The inputs are the horizon $T$, the contexts $\mathcal C = [M]$, the actions $\mathcal A = [K]$, the feedback graph $G = (\mathcal A, E)$, the failure probability $\delta \in (0,1)$, one of two options, and a tie-breaking rule. The algorithm keeps, for each context $c$, an active set $\mathcal A_{\mathrm{act},c}$ (initially $\mathcal A$) and a minimum count $N_c$ (initially $0$), and, for each action $a$, a count $n_a$ shared by all contexts and empirical rewards $\bar r_{c,a}$ for every context (initially $(\bar r_{c,a}, n_a) = (0,0)$). At round $t = 1, \dots, T$:
--
--   1. The context $c_t$ is revealed. Let $\mathcal A_{0,c_t} = \{a \in \mathcal A_{\mathrm{act},c_t} : n_a = N_{c_t}\}$ and let $G_{0,c_t}$ be the restriction of $G$ to $\mathcal A_{0,c_t}$.
--   2. The learner plays $a_t \in \mathcal A_{0,c_t}$ of largest out-degree in $G_{0,c_t}$ (Option I) or of in-degree zero in $G_{0,c_t}$ (Option II), ties broken by the rule.
--   3. The rewards $r_{t,c,a}$ for all $c \in \mathcal C$ and all $a \in I_t = \{a_t\} \cup \{a : (a_t, a) \in E\}$ are revealed; $n_a$ increases by one and $\bar r_{c,a}$ becomes the running mean of the revealed rewards, for every $a \in I_t$ and every $c$.
--   4. For each context $c$: if $\min_{a \in \mathcal A_{\mathrm{act},c}} n_a > N_c$, then $N_c$ is increased and the active set is updated to
--   $$
--   \mathcal A_{\mathrm{act},c} \leftarrow \Big\{a \in \mathcal A_{\mathrm{act},c} : \bar r_{c,a} \ge \max_{b \in \mathcal A_{\mathrm{act},c}} \bar r_{c,b} - 6\sqrt{\frac{\log(2T)\log(MKT/\delta)}{N_c}}\Big\}.
--   $$
--
--   A tie-breaking rule maps the round, the current state of the algorithm (which records the learner's whole observation history: past contexts, actions and revealed rewards), the current context and a set of allowed actions to an action; it is admissible if it picks a member of every nonempty set. Algorithm 1 is Algorithm 2 with $M = 1$, so its width is $6\sqrt{\log(2T)\log(KT/\delta)/N}$.
--
--   **Formalization Note** The text defines $N_c$ as the minimum count $\min_{a \in \mathcal A_{\mathrm{act},c}} n_a$ (pp. 12, 15), while the pseudocode updates $N_c \leftarrow N_c + 1$. The two agree until an elimination removes every active action of count $N_c$; the printed algorithm then meets $\mathcal A_{0,c} = \emptyset$ in a later round and is undefined there. The formalization keeps the text's invariant: in step 4, $N_c$ becomes the new minimum and the active set is pruned with it, repeated until $N_c = \min_{a \in \mathcal A_{\mathrm{act},c}} n_a$. On every run where the printed algorithm is defined, the two algorithms coincide, because counts grow by at most one per round. The empirical reward is $0$ while $n_a = 0$, as in the initialization. "Break ties arbitrarily" is the tie-breaking rule; the theorems hold for every admissible rule. Paper round $t$ is Lean index $t-1$; the state after round $t$ is `elimState … t`.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 12, Algorithm 1; p. 15, Algorithm 2

import Mathlib
import Definitions.Def_FirstPriceLearning_GraphFeedback_FeedbackGraph

namespace FirstPriceLearning.GraphFeedback

/-! Algorithm 2 (Arm Elimination for Stochastic Contextual Bandits with Graph Feedback and Cross
Learning, p. 15) of Han, Zhou, Weissman, arXiv:2003.09795v7, and Algorithm 1 (p. 12) as its
one-context case.

Contexts are `Fin M`, actions `Fin K`, the feedback graph is `E`, the horizon `T` and the failure
probability `δ`. The algorithm is run on a fixed context sequence `ctx : Fin T → Fin M` and the
reward vectors `r : Fin T → Fin M → Fin K → ℝ`, one per round; round `t` of the paper is the Lean
index `t - 1`. Every "break ties arbitrarily" is a tie-breaking rule `tie`, an argument of the
algorithm; the theorems quantify over all of them. -/

/-- The two options of Algorithms 1–2 for choosing `a_t` in `A_0`: Option I (largest out-degree
in `G_0`, any graph) and Option II (in-degree zero in `G_0`, for DAGs). -/
inductive ArmOption
  | optionI
  | optionII

/-- The state of Algorithm 2 after a number of rounds: the active sets `A_{act,c}`, the minimum
counts `N_c`, the action counts `n_a` (shared across contexts), for each `(c, a)` the sum of
the rewards `r_{s,c,a}` over the rounds `s` in which `a` was revealed, and the learner's full
observation history: for each past round `s` (oldest first) the context `c_s`, the action `a_s`
and the revealed rewards `(r_{s,c,b})_{c ∈ C, b ∈ I_s}` (the entries with `b ∉ I_s` are set
to `0`). -/
structure ElimState (M K : ℕ) where
  active : Fin M → Finset (Fin K)
  minCount : Fin M → ℕ
  count : Fin K → ℕ
  rewardSum : Fin M → Fin K → ℝ
  history : List (Fin M × Fin K × (Fin M → Fin K → ℝ))

/-- Initialization: `A_{act,c} = A`, `N_c = 0`, `(r̄_{c,a}, n_a) = (0, 0)`. -/
def ElimState.init (M K : ℕ) : ElimState M K where
  active := fun _ => Finset.univ
  minCount := fun _ => 0
  count := fun _ => 0
  rewardSum := fun _ _ => 0
  history := []

/-- The empirical reward `r̄_{c,a}`: the running mean of the revealed rewards `r_{s,c,a}`
(`0` while `n_a = 0`, as in the initialization). -/
noncomputable def ElimState.empMean {M K : ℕ} (s : ElimState M K) (c : Fin M) (a : Fin K) : ℝ :=
  s.rewardSum c a / s.count a

/-- `A_{0,c} = {a ∈ A_{act,c} : n_a = N_c}`, the active actions pulled the fewest times. -/
def ElimState.leastPulled {M K : ℕ} (s : ElimState M K) (c : Fin M) : Finset (Fin K) :=
  (s.active c).filter (fun a => s.count a = s.minCount c)

open Classical in
/-- The actions of `S = A_0` that the chosen option allows: those of largest out-degree in the
restriction `G_0` of the graph to `S` (Option I), or those of in-degree zero in `G_0`
(Option II). -/
noncomputable def candidates {K : ℕ} (E : Fin K → Fin K → Prop) :
    ArmOption → Finset (Fin K) → Finset (Fin K)
  | .optionI, S => S.filter (fun a => ∀ b ∈ S, outDegreeIn E S b ≤ outDegreeIn E S a)
  | .optionII, S => S.filter (fun a => ∀ b ∈ S, ¬ E b a)

/-- A tie-breaking rule: from the round index, the current state of the algorithm (which
contains the learner's whole observation history), the current context and the set of allowed
actions it returns an action. It sees only what the learner has observed. -/
abbrev TieRule (M K : ℕ) : Type :=
  ℕ → ElimState M K → Fin M → Finset (Fin K) → Fin K

/-- A tie-breaking rule is admissible if it returns a member of every nonempty set it is given. -/
def IsTieRule {M K : ℕ} (tie : TieRule M K) : Prop :=
  ∀ t s c (S : Finset (Fin K)), S.Nonempty → tie t s c S ∈ S

/-- The action chosen by Algorithm 2 at (Lean) round `t` in state `s` under context `c`:
an allowed action of `A_{0,c}`, ties broken by `tie`. -/
noncomputable def chooseAction {M K : ℕ} (E : Fin K → Fin K → Prop) (opt : ArmOption)
    (tie : TieRule M K) (t : ℕ) (s : ElimState M K) (c : Fin M) : Fin K :=
  tie t s c (candidates E opt (s.leastPulled c))

/-- The elimination width `6 √(log(2T) log(MKT/δ) / N)` of Algorithm 2. -/
noncomputable def elimWidth (M K T : ℕ) (δ : ℝ) (N : ℕ) : ℝ :=
  6 * Real.sqrt (Real.log (2 * T) * Real.log (M * K * T / δ) / N)

/-- `min_{a ∈ S} n_a` for a nonempty set `S` of actions (`0` for `S = ∅`, which never occurs
along a run: the active sets stay nonempty). -/
def minCountOn {K : ℕ} (n : Fin K → ℕ) (S : Finset (Fin K)) : ℕ :=
  if h : S.Nonempty then S.inf' h n else 0

/-- The elimination step of Algorithm 2 under context `c` with minimum count `N`: keep the actions
`a ∈ S` with `r̄_{c,a} ≥ max_{b ∈ S} r̄_{c,b} − 6 √(log(2T) log(MKT/δ) / N)`, the empirical
rewards being those of the state `s`. -/
noncomputable def ElimState.prune {M K : ℕ} (s : ElimState M K) (T : ℕ) (δ : ℝ) (c : Fin M)
    (S : Finset (Fin K)) (N : ℕ) : Finset (Fin K) :=
  S.filter (fun a => ∀ b ∈ S, s.empMean c b - elimWidth M K T δ N ≤ s.empMean c a)

/-- One update of the pair `(A_{act,c}, N_c)` once the counts of the state `s` are current: if
`min_{a ∈ A_{act,c}} n_a > N_c`, then `N_c` becomes that minimum and the active set is pruned with
the new `N_c`; otherwise nothing changes. -/
noncomputable def ElimState.refresh {M K : ℕ} (s : ElimState M K) (T : ℕ) (δ : ℝ) (c : Fin M)
    (p : Finset (Fin K) × ℕ) : Finset (Fin K) × ℕ :=
  if p.2 < minCountOn s.count p.1 then
    (s.prune T δ c p.1 (minCountOn s.count p.1), minCountOn s.count p.1)
  else p

open Classical in
/-- One round of Algorithm 2 at Lean round `t`, from state `s`, with context `c` and reward
vector `x = (r_{t,c,a})_{c,a}`: choose `a_t`, reveal `(r_{t,c,b})_{c ∈ C, b ∈ I_t}`, update the
counts and empirical rewards of every `b ∈ I_t` under every context, and then, for each context
`c'`, update `(A_{act,c'}, N_{c'})` by `refresh` until `N_{c'} = min_{a ∈ A_{act,c'}} n_a`
(`K + 1` applications always suffice: each effective application after the first follows one that
removed an action).

When `min_{a ∈ A_{act,c'}} n_a > N_{c'}` the first application is the printed update
`N_{c'} ← N_{c'} + 1` followed by the printed elimination, because the counts grow by at most one
per round. A further application happens only when that elimination removed every active action of
count `N_{c'}`; the printed algorithm would then face `A_{0,c'} = ∅` and is undefined. -/
noncomputable def ElimState.step {M K : ℕ} (E : Fin K → Fin K → Prop) (opt : ArmOption)
    (tie : TieRule M K) (T : ℕ) (δ : ℝ) (t : ℕ) (s : ElimState M K) (c : Fin M)
    (x : Fin M → Fin K → ℝ) : ElimState M K :=
  let a := chooseAction E opt tie t s c
  let s₁ : ElimState M K :=
    { active := s.active
      minCount := s.minCount
      count := fun b => if Revealed E a b then s.count b + 1 else s.count b
      rewardSum := fun c' b => if Revealed E a b then s.rewardSum c' b + x c' b
        else s.rewardSum c' b
      history := s.history ++ [(c, a, fun c' b => if Revealed E a b then x c' b else 0)] }
  let settled : Fin M → Finset (Fin K) × ℕ := fun c' =>
    (s₁.refresh T δ c')^[K + 1] (s.active c', s.minCount c')
  { active := fun c' => (settled c').1
    minCount := fun c' => (settled c').2
    count := s₁.count
    rewardSum := s₁.rewardSum
    history := s₁.history }

/-- The state of Algorithm 2 after the first `t` rounds, run on the context sequence `ctx` and
the reward vectors `r` (the state stays fixed after round `T`). -/
noncomputable def elimState {M K : ℕ} (E : Fin K → Fin K → Prop) (opt : ArmOption)
    (tie : TieRule M K) (T : ℕ) (δ : ℝ) (ctx : Fin T → Fin M)
    (r : Fin T → Fin M → Fin K → ℝ) : ℕ → ElimState M K
  | 0 => ElimState.init M K
  | t + 1 =>
      if h : t < T then
        (elimState E opt tie T δ ctx r t).step E opt tie T δ t (ctx ⟨t, h⟩) (r ⟨t, h⟩)
      else elimState E opt tie T δ ctx r t

/-- The action `a_t` that Algorithm 2 chooses at Lean round `t` (paper round `t + 1`). -/
noncomputable def elimAction {M K : ℕ} (E : Fin K → Fin K → Prop) (opt : ArmOption)
    (tie : TieRule M K) (T : ℕ) (δ : ℝ) (ctx : Fin T → Fin M)
    (r : Fin T → Fin M → Fin K → ℝ) (t : Fin T) : Fin K :=
  chooseAction E opt tie t.val (elimState E opt tie T δ ctx r t.val) (ctx t)

/-- Algorithm 1 (p. 12) is Algorithm 2 with a single context: its reward vectors
`(r_{t,a})_{a ∈ A}` are those of the unique context. -/
def liftOne {K : ℕ} (x : Fin K → ℝ) : Fin 1 → Fin K → ℝ :=
  fun _ => x

/-- The state of Algorithm 1 after the first `t` rounds, on the reward vectors
`r : Fin T → Fin K → ℝ`. Its elimination width is `6 √(log(2T) log(KT/δ) / N)`, since
`M = 1`. -/
noncomputable def alg1State {K : ℕ} (E : Fin K → Fin K → Prop) (opt : ArmOption)
    (tie : TieRule 1 K) (T : ℕ) (δ : ℝ) (r : Fin T → Fin K → ℝ) (t : ℕ) : ElimState 1 K :=
  elimState E opt tie T δ (fun _ => 0) (fun s => liftOne (r s)) t

/-- The action `a_t` that Algorithm 1 chooses at Lean round `t` (paper round `t + 1`). -/
noncomputable def alg1Action {K : ℕ} (E : Fin K → Fin K → Prop) (opt : ArmOption)
    (tie : TieRule 1 K) (T : ℕ) (δ : ℝ) (r : Fin T → Fin K → ℝ) (t : Fin T) : Fin K :=
  elimAction E opt tie T δ (fun _ => 0) (fun s => liftOne (r s)) t

end FirstPriceLearning.GraphFeedback


