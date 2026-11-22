-- Prove2me | Definitions.Def_BeyondDS_Supplement_LocalProtocol
-- name    : BeyondDS_Supplement_LocalProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T05:06:59.333863+00:00
-- url     : https://prove2.me/theorems/5df999f0-f776-43f6-8922-350837a6af3d
-- title:
--   Protocols with arbitrary correlated setup, their executions under a fixed delivery schedule, senders, CSU and broadcast
-- statement:
--   This is the protocol class of the paper's lower bounds (§12 and Proposition 6.3).
--
--   **Protocols.** A protocol for $n$ players with input type $I$ consists of a probability space $(\Omega,\mu)$, an initial-state map, a local step and a decision read-out. One sample $\omega\in\Omega$ holds the whole setup: the public information, all private initial states with arbitrary correlations among them, every private random tape and any common randomness. Its law $\mu$ does not depend on the inputs. Player $i$ with input $a$ starts in the state $\mathrm{init}(\omega,i,a)$. At each step, player $i$ in state $s$ receives the list of messages delivered to it, each with its immediate sender, and $\mathrm{step}(i,s,\text{inbox})$ returns its new state and the messages it sends, each with its recipient. A state may record a decision, and a player's decision is the first one recorded. States and messages are arbitrary, and executions are unbounded.
--
--   **Executions.** A delivery schedule is a function $\mathrm{delay}(t,i,j)\in\mathbb N$: a message sent at step $t$ by $i$ to $j$ is delivered at step $t+1+\mathrm{delay}(t,i,j)$. The schedule is fixed in advance and is the same in all executions compared; $\mathrm{delay}=0$ is synchronous delivery. For an input assignment $x$ and a sample $\omega$, this determines the whole execution.
--
--   **Measures.** A message to oneself is a free local step. A **sender** is a player that sends at least one message to another player at some step of the execution, including after it has decided. For a set $F$ of passively corrupt players, $M$ is the number of senders outside $F$ and $K\in[0,\infty]$ is the total number of messages sent to other players by players outside $F$. A protocol is a **multicast** protocol if, whenever a player sends a message to another player, at the same step it sends that message to every other player.
--
--   **CSU.** With binary inputs, consensus with strong unanimity holds for the honest players (those outside $F$) in an execution if each of them decides, their decisions agree, and whenever all their inputs equal $b$ each of their decisions is $b$. The protocol has CSU error at most $\eta$ against the static passive adversaries if this holds with probability at least $1-\eta$ for every $F$ with $|F|\le f$ and every input assignment. A passive corruption changes only which players count as honest; the execution is the same.
--
--   **Broadcast.** For Byzantine broadcast with designated sender $s$, only $s$ has an input bit $b$. The fault-free execution succeeds if every player decides and every decision is $b$.
--
--   These notions are shared by Theorems 5 and 11 and by the optimality clause of Theorem 2.
--
--   **Formalization Note** The local machines are deterministic functions of $\omega$, so all randomness is in $\mu$; independence of the private tapes is not required. The probability space is a general measure space, and `MeasurableRun` is the standing convention that, at each step, the number of messages a player sends and its recorded decision are measurable in $\omega$.
-- source:
--   Rambaud, Beyond Dolev–Strong: Adaptive Byzantine Broadcast with Õ(n^{3/2}) Messages at a Tight Honest Majority, STOC 2027 submission (manuscript sha256 c84cf9c9…), §12, pp.57–59 (PDF pp.58–60), model and error event, multicast consequence; Proposition 6.3, p.21 (PDF p.22); §4.2, p.12 (PDF p.13)

import Mathlib

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace BeyondDS.Supplement

/-- A protocol in the lower-bound model of Rambaud, *Beyond Dolev–Strong*, STOC 2027 submission (manuscript
sha256 c84cf9c9…), §12, p.57 (PDF 58), which is also the protocol class of Proposition 6.3, p.21 (PDF 22):
"a setup samples public information and a tuple of private initial states from an arbitrary joint
distribution that is independent of that vector. […] After setup, players receive binary inputs and
communicate through point-to-point channels. […] All subsequent observations are determined by this initial
state, local inputs and randomness, and delivered point-to-point messages."

* `Ω`, `μ`: one probability space holding the setup (public information and all private initial states, with
  arbitrary correlations), every private random tape and any common randomness. It does not depend on the
  inputs.
* `init ω i a`: the initial local state of player `i` with input `a`.
* `step i s inbox`: one local step of player `i` in state `s`, given the messages delivered to it at this
  step as `(immediate sender, message)` pairs; it returns the new state and the messages it sends, as
  `(recipient, message)` pairs.
* `out s`: the decision recorded in a state, if any; a player's decision is the first one.

**Formalization Note.** Local machines are deterministic functions of `ω`, so all randomness is in `μ`;
independence of the tapes is not required, which only enlarges the class. States, messages and the
probability space are arbitrary types; executions are unbounded. A message is one point-to-point send of
arbitrary content ("arbitrary batching", p.21). -/
structure LocalProtocol (n : ℕ) (In : Type) where
  St : Type
  Msg : Type
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  μ : Measure Ω
  [isProb : IsProbabilityMeasure μ]
  init : Ω → Fin n → In → St
  step : Fin n → St → List (Fin n × Msg) → St × List (Fin n × Msg)
  out : St → Option Bool

attribute [instance] LocalProtocol.mΩ LocalProtocol.isProb

/-- A message in transit: its delivery step, its sender, its recipient and its contents. -/
structure Transit (n : ℕ) (Msg : Type) where
  due : ℕ
  src : Fin n
  dst : Fin n
  msg : Msg

namespace LocalProtocol

variable {n : ℕ} {In : Type} (P : LocalProtocol n In)

/-- The messages delivered to `i` at step `t`, in the order in which they were sent. -/
def inboxOf (tr : List (Transit n P.Msg)) (t : ℕ) (i : Fin n) : List (Fin n × P.Msg) :=
  (tr.filter fun m => decide (m.due = t ∧ m.dst = i)).map fun m => (m.src, m.msg)

/-- The execution under a fixed delivery schedule (§12, p.57: "Fix a permitted delivery schedule that is the
same in all executions compared below, for example delivery at the end of each synchronous round"). Time is a
sequence of steps `0, 1, 2, …`; a message sent at step `t` by `i` to `j` is delivered at step
`t + 1 + delay t i j`. `run delay x ω t` is the configuration before step `t`: every local state and every
message sent so far. The schedule depends on nothing but the step and the two endpoints, so it cannot convey
inputs or corruption status. `delay = 0` is synchronous delivery. -/
def run (delay : ℕ → Fin n → Fin n → ℕ) (x : Fin n → In) (ω : P.Ω) :
    ℕ → (Fin n → P.St) × List (Transit n P.Msg)
  | 0 => (fun i => P.init ω i (x i), [])
  | t + 1 =>
    let c := run delay x ω t
    let res : Fin n → P.St × List (Fin n × P.Msg) := fun i => P.step i (c.1 i) (P.inboxOf c.2 t i)
    (fun i => (res i).1,
      c.2 ++ (List.finRange n).flatMap fun i =>
        (res i).2.map fun o => ⟨t + 1 + delay t i o.1, i, o.1, o.2⟩)

/-- The messages player `i` sends at step `t`. -/
def sendsAt (delay : ℕ → Fin n → Fin n → ℕ) (x : Fin n → In) (ω : P.Ω) (t : ℕ) (i : Fin n) :
    List (Fin n × P.Msg) :=
  (P.step i ((P.run delay x ω t).1 i) (P.inboxOf (P.run delay x ω t).2 t i)).2

/-- The number of point-to-point messages `i` sends at step `t`. A message to oneself is a free local
step and is not counted. -/
def sentAt (delay : ℕ → Fin n → Fin n → ℕ) (x : Fin n → In) (ω : P.Ω) (t : ℕ) (i : Fin n) : ℕ :=
  ((P.sendsAt delay x ω t i).filter fun o => decide (o.1 ≠ i)).length

/-- All point-to-point messages `i` sends in the whole execution, in `[0, ∞]`: "Sends are counted throughout
the execution, including after a decision and on failure histories" (§12, p.57). -/
noncomputable def sentBy (delay : ℕ → Fin n → Fin n → ℕ) (x : Fin n → In) (ω : P.Ω) (i : Fin n) : ℝ≥0∞ :=
  ∑' t : ℕ, (P.sentAt delay x ω t i : ℝ≥0∞)

/-- "A sender is a player that sends at least one point-to-point message during the execution" (§12, p.57). -/
def IsSender (delay : ℕ → Fin n → Fin n → ℕ) (x : Fin n → In) (ω : P.Ω) (i : Fin n) : Prop :=
  ∃ t, P.sentAt delay x ω t i ≠ 0

/-- The decision of `i`: the first decision its state records, and `none` if it never decides. -/
noncomputable def decision (delay : ℕ → Fin n → Fin n → ℕ) (x : Fin n → In) (ω : P.Ω) (i : Fin n) :
    Option Bool := by
  classical
  exact
    if h : ∃ t, (P.out ((P.run delay x ω t).1 i)).isSome = true then
      P.out ((P.run delay x ω (Nat.find h)).1 i)
    else none

/-- `M` of §12: "In this section only, M denotes the number of distinct honest senders", the honest players
being those outside the corrupt set `F`. -/
noncomputable def numSenders (delay : ℕ → Fin n → Fin n → ℕ) (F : Finset (Fin n)) (x : Fin n → In)
    (ω : P.Ω) : ℕ := by
  classical
  exact ((Finset.univ \ F).filter fun i => P.IsSender delay x ω i).card

/-- `K` of §12, p.59 and the honest-message count of Proposition 6.3: "the total number of point-to-point
messages sent by honest players", in `[0, ∞]`. -/
noncomputable def numMsgs (delay : ℕ → Fin n → Fin n → ℕ) (F : Finset (Fin n)) (x : Fin n → In)
    (ω : P.Ω) : ℝ≥0∞ :=
  ∑ i ∈ Finset.univ \ F, P.sentBy delay x ω i

/-- The standing measurability convention: at every step, the number of messages each player sends and each
player's recorded decision are measurable functions of the randomness. It holds for every protocol on a
countable probability space with all sets measurable, and for every protocol whose local states are
measurable functions of finitely many bits of its tapes. -/
def MeasurableRun (delay : ℕ → Fin n → Fin n → ℕ) : Prop :=
  (∀ (x : Fin n → In) (t : ℕ) (i : Fin n), Measurable fun ω => P.sentAt delay x ω t i) ∧
  (∀ (x : Fin n → In) (t : ℕ) (i : Fin n) (b : Bool),
    MeasurableSet {ω | P.out ((P.run delay x ω t).1 i) = some b})

/-- "A multicast sends the same message to all other n − 1 players and costs n − 1 point-to-point messages.
In a protocol in which every honest send is a multicast …" (§12, p.59): whenever a player sends a message to
another player, at the same step it sends that message to every other player. A message to oneself is a free
local step, not a send, and is not constrained. -/
def IsMulticast (delay : ℕ → Fin n → Fin n → ℕ) : Prop :=
  ∀ (x : Fin n → In) (ω : P.Ω) (t : ℕ) (i : Fin n), ∀ o ∈ P.sendsAt delay x ω t i, o.1 ≠ i →
    ∀ j : Fin n, j ≠ i → (j, o.2) ∈ P.sendsAt delay x ω t i

end LocalProtocol

namespace LocalProtocol

variable {n : ℕ} (P : LocalProtocol n Bool)

/-- CSU, consensus with strong unanimity (§12, p.57), for the honest players, those outside `F`: "every honest
player must decide, honest decisions must agree, and equal honest inputs must force that common input as the
decision". -/
def CSU (delay : ℕ → Fin n → Fin n → ℕ) (F : Finset (Fin n)) (x : Fin n → Bool) (ω : P.Ω) : Prop :=
  (∀ i, i ∉ F → (P.decision delay x ω i).isSome = true) ∧
  (∀ i j, i ∉ F → j ∉ F → ∀ b b', P.decision delay x ω i = some b →
    P.decision delay x ω j = some b' → b = b') ∧
  (∀ b : Bool, (∀ i, i ∉ F → x i = b) → ∀ i, i ∉ F → ∀ b',
    P.decision delay x ω i = some b' → b' = b)

/-- CSU error at most `η` (§12, p.57) against the static passive adversaries: for every corrupt set `F` of at
most `f` players whose members "receive their corresponding states and may execute the honest code", and every
input assignment, the three properties hold jointly with probability at least `1 − η`. A passive corruption
changes only which players are honest; "the full distribution of honest-code behavior is identical … the
corruption labels alone change" (p.58). -/
def CSUErrorLE (delay : ℕ → Fin n → Fin n → ℕ) (f : ℕ) (η : ℝ) : Prop :=
  ∀ (F : Finset (Fin n)), F.card ≤ f → ∀ x : Fin n → Bool,
    ENNReal.ofReal (1 - η) ≤ P.μ {ω | P.CSU delay F x ω}

end LocalProtocol

/-- Inputs of Byzantine broadcast with designated sender `s`: only `s` receives the bit `b`. -/
def bcastInput {n : ℕ} (s : Fin n) (b : Bool) : Fin n → Option Bool :=
  fun i => if i = s then some b else none

/-- Byzantine broadcast succeeds in the fault-free execution with sender `s` and input `b` (§4.2, p.12): every
player decides, the decisions coincide, and they equal the sender's input. -/
def LocalProtocol.BroadcastOK {n : ℕ} (P : LocalProtocol n (Option Bool))
    (delay : ℕ → Fin n → Fin n → ℕ) (s : Fin n) (b : Bool) (ω : P.Ω) : Prop :=
  (∀ i, (P.decision delay (bcastInput s b) ω i).isSome = true) ∧
  (∀ i j b₁ b₂, P.decision delay (bcastInput s b) ω i = some b₁ →
    P.decision delay (bcastInput s b) ω j = some b₂ → b₁ = b₂) ∧
  (∀ i b', P.decision delay (bcastInput s b) ω i = some b' → b' = b)

end BeyondDS.Supplement


