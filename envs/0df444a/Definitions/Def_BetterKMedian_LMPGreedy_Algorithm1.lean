-- Prove2me | Definitions.Def_BetterKMedian_LMPGreedy_Algorithm1
-- name    : BetterKMedian_LMPGreedy_Algorithm1
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:19:53.207559+00:00
-- url     : https://prove2.me/theorems/e53e25f8-b6a2-4a0b-a3c1-6e45358478dc
-- title:
--   Algorithm 1 — the greedy algorithm with general bids, as a set of executions
-- statement:
--   Algorithm 1 runs with a bidding function $\beta$ and an opening cost $\hat f$. Its state (`AlgState`) is the set $A$ of active clients, the set $S$ of open facilities and the frozen values $\alpha_j$ of inactive clients; every active client has $\alpha_j=\alpha$, the global time. Initially $A=D$, $S=\emptyset$, $\alpha=0$. The bid of $j$ to $i$ at time $t$ is $\beta(t,d(i,j))$ if $j\in A$ and $\beta(d(j,S),d(i,j))$ otherwise (`bid`).
--
--   **Event 1** at time $t$ (`Event1`): an unopened $i\in F$ with $\sum_{j\in D}\mathrm{bid}(j,i)=\hat f$; processing it opens $i$ and removes every active $j$ with $\alpha_j=t\ge d(j,S\cup\{i\})$, freezing $\alpha_j=t$. **Event 2** (`Event2`): an active $j$ with $t=d(i,j)$ for an open $i$; processing it removes $j$, freezing $\alpha_j=t$.
--
--   An **execution** (`IsExecution β f̂ steps`) is a finite list of events with times such that: times start at $0$ and never decrease; each event's condition holds, in the current state, at its time; at every time from the previous event's time (inclusive) to the event's time (exclusive) no event condition holds (so $\alpha$ "increases until the first event", and no unopened facility is ever over-paid); an event is processed only while $A\ne\emptyset$, or at the same time as the previous event (pending simultaneous events, in any order); and $A=\emptyset$ at the end. Every tie-breaking order is a different execution. The output $S^\star$ (`output`) is the final set of open facilities.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (2026), STOC 2027 submission, SHA-256 5c2605b2…f461, Algorithm 1, printed p. 8 (PDF 10)

import Mathlib
import Definitions.Def_BetterKMedian_LMPGreedy_UFL

set_option autoImplicit false

/-!
# Algorithm 1 (Greedy with a generalized bidding strategy) as a set of executions

Buhai et al., *A Better-than-2 Approximation for k-Median* (2026), STOC 2027 submission,
SHA-256 5c2605b2…f461, Algorithm 1, printed p. 8 (PDF 10).

Algorithm 1 is run with a bidding function `β` and an opening cost `f̂` (the paper runs it with
`f̂ = ρ · f`, and measures the LMP guarantee with respect to `f`). Its state is the set `A` of
active clients, the set `S` of opened facilities, the global time `α`, and the frozen values
`α_j` of the clients that are no longer active. Every active client has `α_j = α`.

An execution is the finite list of the events it processes, in order, each with the time `α` at
which it is processed:
* `Ev.open_ i` — Event 1: the unopened facility `i ∈ F` is fully paid for,
  `Σ_{j ∈ D} bid(j, i) = f̂`; open it, then remove from `A` every active `j` with
  `α_j ≥ d(j, S)` (lines 6–8);
* `Ev.serve j` — Event 2: the active client `j` reaches an open facility `i ∈ S`,
  `α_j = d(i, j)`; remove `j` from `A` (lines 9–10).

The rules of a valid execution (`IsExecution`):
* times start at `0` and never decrease;
* "Increase `α` uniformly until one of the following events occurs" (line 5): at every time `u`
  from the previous event's time (inclusive) to this event's time (exclusive), no event
  condition holds in the current state — so no unopened facility is ever over-paid and no
  active client passes an open facility;
* the event condition holds, in the current state, at the event's time;
* the loop runs while `A ≠ ∅` (line 4); simultaneous events are processed one at a time in an
  arbitrary order, so an event at the same time as the previous event is also allowed after `A`
  became empty (any order of the events pending at that time);
* the execution ends with `A = ∅`.
Every tie-breaking order is a different execution; the theorems quantify over all of them.
-/

namespace BetterKMedian.LMPGreedy

/-- An event processed by Algorithm 1. -/
inductive Ev (N : ℕ) where
  /-- Event 1: open facility `i` -/
  | open_ (i : Fin N)
  /-- Event 2: active client `j` reaches an open facility and is served -/
  | serve (j : Fin N)

/-- One processed event together with the global time `α` at which it is processed. -/
structure Step (N : ℕ) where
  /-- the global time `α` of the event -/
  time : ℝ
  /-- the event -/
  ev : Ev N

/-- The state of Algorithm 1: active clients `A`, open facilities `S`, and the frozen value
`α_j` of every client that is no longer active (the entry of an active client is unused: its
value is the current global time). -/
structure AlgState (N : ℕ) where
  /-- the active clients `A` -/
  active : Finset (Fin N)
  /-- the opened facilities `S` -/
  opened : Finset (Fin N)
  /-- frozen values `α_j` of inactive clients -/
  alpha : Fin N → ℝ

namespace Instance

variable (I : Instance)

/-- Line 1: `A = D`, `S = ∅`, `α = 0`. -/
def initState : AlgState I.N where
  active := I.clients
  opened := ∅
  alpha := fun _ => 0

/-- Line 3: the bid of client `j` to facility `i` at global time `t` in state `σ`:
`β(α_j, d(i, j)) = β(t, d(i, j))` if `j ∈ A`, and `β(d(j, S), d(i, j))` if `j ∉ A`. -/
noncomputable def bid (β : ℝ → ℝ → ℝ) (σ : AlgState I.N) (t : ℝ) (j i : Fin I.N) : ℝ := by
  classical
  exact if j ∈ σ.active then β t (I.d i j) else β (I.distToSet σ.opened j) (I.d i j)

/-- Event 1 condition (line 6) at time `t`: `i ∈ F` is unopened and fully paid for,
`Σ_{j ∈ D} bid(j, i) = f̂`. -/
def Event1 (β : ℝ → ℝ → ℝ) (fhat : ℝ) (σ : AlgState I.N) (t : ℝ) (i : Fin I.N) : Prop :=
  i ∈ I.facilities ∧ i ∉ σ.opened ∧ (∑ j ∈ I.clients, I.bid β σ t j i) = fhat

/-- Event 2 condition (line 9) at time `t`: `j ∈ A` and `α_j = t = d(i, j)` for an open `i`. -/
def Event2 (σ : AlgState I.N) (t : ℝ) (j : Fin I.N) : Prop :=
  j ∈ σ.active ∧ ∃ i ∈ σ.opened, t = I.d i j

/-- The condition of the event `e` holds in state `σ` at time `t`. -/
def EventHolds (β : ℝ → ℝ → ℝ) (fhat : ℝ) (σ : AlgState I.N) (t : ℝ) : Ev I.N → Prop
  | .open_ i => I.Event1 β fhat σ t i
  | .serve j => I.Event2 σ t j

/-- No event condition holds in state `σ` at time `u`. -/
def NoEvent (β : ℝ → ℝ → ℝ) (fhat : ℝ) (σ : AlgState I.N) (u : ℝ) : Prop :=
  (∀ i : Fin I.N, ¬ I.Event1 β fhat σ u i) ∧ (∀ j : Fin I.N, ¬ I.Event2 σ u j)

/-- Processing an event at time `t` (lines 7–8 and 10). Event 1 opens `i` and removes every
active `j` with `α_j = t ≥ d(j, S ∪ {i})`, freezing `α_j = t`; Event 2 removes `j`, freezing
`α_j = t`. -/
noncomputable def applyStep (σ : AlgState I.N) (s : Step I.N) : AlgState I.N := by
  classical
  exact match s.ev with
  | .open_ i =>
      let S' := insert i σ.opened
      let removed := σ.active.filter (fun j => I.distToSet S' j ≤ s.time)
      { active := σ.active \ removed
        opened := S'
        alpha := fun j => if j ∈ removed then s.time else σ.alpha j }
  | .serve j =>
      { active := σ.active.erase j
        opened := σ.opened
        alpha := fun j' => if j' = j then s.time else σ.alpha j' }

/-- The state after the first `k` events of the list `steps`. -/
noncomputable def stateAfter (steps : List (Step I.N)) (k : ℕ) : AlgState I.N :=
  (steps.take k).foldl I.applyStep I.initState

/-- The time of the event processed before the event of index `k` (0-based): `0` for the first
event (the time starts at `α = 0`). -/
def prevTime (steps : List (Step I.N)) (k : ℕ) : ℝ :=
  match k with
  | 0 => 0
  | k + 1 => (steps[k]?.map Step.time).getD 0

/-- `steps` is an execution of Algorithm 1 with bidding function `β` and opening cost `f̂` on
the instance (all rules listed in the module docstring). -/
def IsExecution (β : ℝ → ℝ → ℝ) (fhat : ℝ) (steps : List (Step I.N)) : Prop :=
  (∀ (k : ℕ) (hk : k < steps.length),
      let σ := I.stateAfter steps k
      let s := steps[k]
      I.prevTime steps k ≤ s.time ∧
      (σ.active.Nonempty ∨ (0 < k ∧ s.time = I.prevTime steps k)) ∧
      I.EventHolds β fhat σ s.time s.ev ∧
      ∀ u : ℝ, I.prevTime steps k ≤ u → u < s.time → I.NoEvent β fhat σ u) ∧
  (I.stateAfter steps steps.length).active = ∅

/-- The final state of an execution. -/
noncomputable def finalState (steps : List (Step I.N)) : AlgState I.N :=
  I.stateAfter steps steps.length

/-- The output `S⋆` of an execution: the set of facilities open at termination. -/
noncomputable def output (steps : List (Step I.N)) : Finset (Fin I.N) :=
  (I.finalState steps).opened

end Instance

end BetterKMedian.LMPGreedy


