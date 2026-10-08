-- Prove2me | Definitions.Def_DLSConsensus_LowerBound_Model
-- name    : DLSConsensus_LowerBound_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:24:17.040333+00:00
-- url     : https://prove2.me/theorems/e675d589-6586-4268-8a59-31a53e2b2318
-- title:
--   The step-level model (Sections 2.1–2.4): protocols, runs, fail-stop faults with Φ = 1, partially synchronous communication, t-resilient consensus with weak unanimity
-- statement:
--   This file fixes the model of computation of Dwork, Lynch and Stockmeyer (§§2.1–2.4) in the case used by their lower bound for fail-stop faults: synchronous processors ($\Phi = 1$), partially synchronous communication, binary values.
--
--   **Processors and protocols.** There are $N$ processors $p_1, \dots, p_N$ and a set of initial values $V = \{0, 1\}$. Each processor follows a deterministic protocol given by a state transition diagram over a set $\Sigma$ of states (possibly infinite) and a set $\mathcal M$ of message contents (possibly infinite): an initial state $\mathrm{init}_i(v_i)$ determined by the initial value $v_i$; for each state, the next instruction, which is either
--   1. $\mathrm{Send}(m, p_j)$, placing $m$ in $p_j$'s buffer, followed by a next state depending only on the current state, or
--   2. $\mathrm{Receive}(p_i)$, removing some (possibly empty) set $S$ of messages from $p_i$'s buffer and delivering them, followed by a next state depending on the current state and on $S$;
--
--   and, for each state, a recorded decision (none, $0$ or $1$). A processor *decides* $v$ at time $n$ if its state after tick $n$ records $v$ and no earlier state records a decision; only the first decision counts, so deciding is irreversible.
--
--   **Runs.** Real time is the ticks $1, 2, 3, \dots$. A run fixes the initial values and, for each tick, which processors take a step, the resulting states, and the set of messages delivered by each Receive. A processor that takes a step executes the instruction of its current state; a processor that does not step keeps its state. A message is delivered only by a Receive of its addressee, only after the tick at which it was sent, and at most once. Every run is infinite.
--
--   **Faults and processor synchrony.** For a set $C$ of processors (the correct ones), a run is *fail-stop with $\Phi = 1$* if every processor of $C$ takes a step at every tick, and every other processor may skip ticks before a stop time, after which it never steps (stop time $0$: initially dead).
--
--   **Communication synchrony.** For a positive integer $\Delta$, the bound $\Delta$ *holds in $[T, \infty)$* for a run if every message placed in $p_j$'s buffer at a tick $s_1 \ge T$ is delivered to $p_j$ no later than any Receive of $p_j$ at a tick $s_2 \ge s_1 + \Delta$. A run is allowed when *$\Delta$ holds eventually* if $\Delta$ holds in $[T, \infty)$ for some $T$ (the global stabilization time), and allowed when *delta is unknown* if some positive $\Delta$ holds in $[1, \infty)$.
--
--   **Correctness.** A protocol is a *$t$-resilient consensus protocol achieving weak unanimity* for a communication model if for every set $C$ of at least $N - t$ processors and every allowed fail-stop run with correct set $C$:
--   1. (consistency) no two processors of $C$ decide differently;
--   2. (termination) every processor of $C$ decides;
--   3. (weak unanimity) if all initial values are $v$ and $C$ contains all processors, every processor that decides decides $v$.
--
--   The file also names the runs of Scenarios A and B of the proof of Theorem 4.3: all initial values equal to $v$, the processors of a group $S$ step at every tick, the others are initially dead, and every message from $S$ to $S$ is delivered in time $1$, that is, no later than the addressee's first Receive at least one tick after it was sent.
--
--   These definitions are the vocabulary of every statement of the mission.
--
--   **Formalization Note** Processor $p_i$ is the index $i - 1$ of `Fin N`. A message instance is identified by its sender and the tick at which it was sent; a Receive passes each delivered message to the protocol as (sender, content). The absolute send tick identifies the buffered instance but is not exposed to the protocol. A step is a Send to one processor or a Receive, never both (Technical Remark (1)). Fail-stop processors may skip ticks before their final stop; $\Phi$ constrains correct processors only. A faulty processor that never stops is not modelled separately: such a run is covered by enlarging $C$. "Δ is a positive integer" is the well-formedness condition `Comm.WF`.
-- source:
--   Dwork, Lynch, Stockmeyer, Consensus in the presence of partial synchrony, J. ACM 35 (1988), p. 292 Technical Remark (1); p. 293 Section 2.1 and Section 2.2 (fail-stop); p. 294 Section 2.3; pp. 294–295 Section 2.4; p. 303 (Φ = 1); pp. 305–306 proof of Theorem 4.3 (Scenarios A and B)

import Mathlib

namespace DLSConsensus.LowerBound

/-! The step-level model of computation of Dwork, Lynch, Stockmeyer, *Consensus in the presence of
partial synchrony*, J. ACM 35 (1988): §2.1 (p. 293), §2.2 fail-stop faults (p. 293), §2.3 partial
synchrony (p. 294), §2.4 correctness (pp. 294–295), Technical Remark (1) (p. 292), specialised to
synchronous processors (Φ = 1, §4, p. 303) and binary values.

Conventions: the processors p_1, …, p_N are the indices `0, …, N - 1` of `Fin N`; real time is the
ticks `1, 2, 3, …`; `R.state i n` is the state of processor `i` after the first `n` ticks (so
`R.state i 0` is its initial state). A message instance is identified by the pair `(k, s)`: the
processor `k` that sent it and the tick `s` at which it was sent (a processor sends at most one
message per tick). -/

/-- An instruction (§2.1, p. 293; Technical Remark (1), p. 292): `send m j next` is `Send(m, p_j)`
followed by the state `next`; `receive next` is `Receive(p_i)`, whose next state is `next S` for the
set `S` of delivered messages. A delivered message is given to the receiver as
`(sender, content)`; the send tick identifies the buffered instance but is not revealed. -/
inductive Instr (N : ℕ) (σ M : Type) where
  | send (m : M) (j : Fin N) (next : σ)
  | receive (next : Set (Fin N × M) → σ)

/-- Whether an instruction is a `Receive`. -/
def Instr.IsReceive {N : ℕ} {σ M : Type} : Instr N σ M → Prop
  | .send _ _ _ => False
  | .receive _ => True

/-- A deterministic protocol for `N` processors with binary initial values (§2.1, p. 293): per
processor, the initial state determined by the initial value, the instruction to execute in each
state, and the decision recorded in each state (`none` = undecided). -/
structure Protocol (N : ℕ) (σ M : Type) where
  init : Fin N → Bool → σ
  instr : Fin N → σ → Instr N σ M
  decision : Fin N → σ → Option Bool

/-- A run (§2.1, p. 293): the initial values, which processors take a step at each tick, the state of
each processor after each tick, and the set of message instances `(k, s)` delivered to each
processor at each tick. Its consistency with a protocol is `IsRun`. -/
structure Run (N : ℕ) (σ : Type) where
  val : Fin N → Bool
  active : Fin N → ℕ → Prop
  state : Fin N → ℕ → σ
  deliv : Fin N → ℕ → Set (Fin N × ℕ)

variable {N : ℕ} {σ M : Type}

/-- In run `R`, processor `k` executes `Send(m, p_j)` at tick `s` (so `s ≥ 1`). -/
def Sends (π : Protocol N σ M) (R : Run N σ) (k : Fin N) (s : ℕ) (j : Fin N) (m : M) : Prop :=
  ∃ n, s = n + 1 ∧ R.active k s ∧ ∃ nx, π.instr k (R.state k n) = Instr.send m j nx

/-- In run `R`, processor `j` executes a `Receive(p_j)` at tick `s` (so `s ≥ 1`). -/
def ReceivesAt (π : Protocol N σ M) (R : Run N σ) (j : Fin N) (s : ℕ) : Prop :=
  ∃ n, s = n + 1 ∧ R.active j s ∧ (π.instr j (R.state j n)).IsReceive

/-- The set `S` of messages delivered to `i` at tick `n`, as `(sender, content)`. The send tick
identifies a buffered instance in `R.deliv` without giving the protocol a real-time clock. -/
def delivered (π : Protocol N σ M) (R : Run N σ) (i : Fin N) (n : ℕ) : Set (Fin N × M) :=
  {x | ∃ s, (x.1, s) ∈ R.deliv i n ∧ Sends π R x.1 s i x.2}

/-- `R` is a run of protocol `π` (§2.1, p. 293): processors start in the state given by their initial
value; a processor that takes no step keeps its state; a step executes the instruction of the current
state; messages are delivered only by a `Receive`, only from the receiver's buffer (sent to it at an
earlier tick), and each message at most once. -/
def IsRun (π : Protocol N σ M) (R : Run N σ) : Prop :=
  (∀ i, R.state i 0 = π.init i (R.val i)) ∧
  (∀ i n, ¬ R.active i (n + 1) → R.state i (n + 1) = R.state i n) ∧
  (∀ i n (m : M) j nx, R.active i (n + 1) → π.instr i (R.state i n) = Instr.send m j nx →
    R.state i (n + 1) = nx) ∧
  (∀ i n f, R.active i (n + 1) → π.instr i (R.state i n) = Instr.receive f →
    R.state i (n + 1) = f (delivered π R i (n + 1))) ∧
  (∀ i n k s, (k, s) ∈ R.deliv i n →
    ReceivesAt π R i n ∧ s < n ∧ ∃ m : M, Sends π R k s i m) ∧
  (∀ i n n' k s, (k, s) ∈ R.deliv i n → (k, s) ∈ R.deliv i n' → n = n')

/-- Fail-stop faults with synchronous processors, Φ = 1 (§2.2, p. 293; §2.3, p. 294; §4, p. 303):
every processor of `C` (the correct ones) takes a step at every tick `n ≥ 1`; every other processor
has a stop time `T` after which it takes no steps (`T = 0`: initially dead). Before `T`, the
processor may skip ticks: Φ constrains correct processors only. -/
def FailStop (C : Finset (Fin N)) (R : Run N σ) : Prop :=
  (∀ i ∈ C, ∀ n, 1 ≤ n → R.active i n) ∧
  (∀ i ∉ C, ∃ T : ℕ, ∀ n, T ≤ n → ¬ R.active i n)

/-- The communication bound `Δ` holds in `[T, ∞)` for run `R` (§2.3, p. 294): if `m` is placed in
`p_j`'s buffer by a `Send(m, p_j)` at a tick `s₁ ≥ T`, and `p_j` executes a `Receive(p_j)` at a tick
`s₂ ≥ s₁ + Δ`, then `m` is delivered to `p_j` at tick `s₂` or earlier. -/
def DeltaHoldsFrom (π : Protocol N σ M) (Δ T : ℕ) (R : Run N σ) : Prop :=
  ∀ k s j (m : M) s₂, Sends π R k s j m → T ≤ s → s + Δ ≤ s₂ → ReceivesAt π R j s₂ →
    ∃ n ≤ s₂, (k, s) ∈ R.deliv j n

/-- The two models of partially synchronous communication (§2.3, p. 294): `eventually Δ` (Δ holds
eventually, for the fixed `Δ`) and `unknown` (delta is unknown). -/
inductive Comm where
  | eventually (Δ : ℕ)
  | unknown

/-- Well-formedness: `Δ` is a positive integer (§2.3, p. 294). -/
def Comm.WF : Comm → Prop
  | .eventually Δ => 0 < Δ
  | .unknown => True

/-- The runs allowed by a communication model (§2.3, p. 294): for `eventually Δ`, those with a time
`T` (the GST) such that `Δ` holds in `[T, ∞)`; for `unknown`, those with a positive `Δ` that holds in
`[1, ∞)`. -/
def Comm.Allowed (π : Protocol N σ M) : Comm → Run N σ → Prop
  | .eventually Δ, R => ∃ T : ℕ, DeltaHoldsFrom π Δ T R
  | .unknown, R => ∃ Δ : ℕ, 0 < Δ ∧ DeltaHoldsFrom π Δ 1 R

/-- Processor `i` decides `v` at tick `n` in `R`: its state after tick `n` records the decision `v`,
and no earlier state records a decision. Deciding is irreversible: only the first decision counts. -/
def DecidesAt (π : Protocol N σ M) (R : Run N σ) (i : Fin N) (v : Bool) (n : ℕ) : Prop :=
  π.decision i (R.state i n) = some v ∧ ∀ n' < n, π.decision i (R.state i n') = none

/-- Processor `i` decides `v` in `R`. -/
def Decides (π : Protocol N σ M) (R : Run N σ) (i : Fin N) (v : Bool) : Prop :=
  ∃ n, DecidesAt π R i v n

/-- `π` is a `t`-resilient consensus protocol achieving weak unanimity for fail-stop faults, synchronous
processors (Φ = 1) and the communication model `cm` (§2.4, pp. 294–295): for every set `C` of at least
`N - t` processors and every allowed run in which the processors of `C` are correct and the others
fail-stop, (consistency) no two processors of `C` decide differently, (termination) every processor of
`C` decides, and (weak unanimity) if all initial values are `v` and `C` contains all processors, then
every processor that decides decides `v`. -/
def Resilient (π : Protocol N σ M) (t : ℕ) (cm : Comm) : Prop :=
  ∀ C : Finset (Fin N), N - t ≤ C.card → ∀ R : Run N σ, IsRun π R → FailStop C R →
    cm.Allowed π R →
      (∀ i ∈ C, ∀ j ∈ C, ∀ v w, Decides π R i v → Decides π R j w → v = w) ∧
      (∀ i ∈ C, ∃ v, Decides π R i v) ∧
      (C = Finset.univ → ∀ v, (∀ i, R.val i = v) → ∀ i w, Decides π R i w → w = v)

/-- Messages between processors of `S` are delivered in time 1 (proof of Theorem 4.3, p. 305): a
message sent by `k ∈ S` to `j ∈ S` at tick `s` is delivered to `j` no later than its first `Receive`
at a tick `≥ s + 1`. -/
def TimeOneWithin (π : Protocol N σ M) (S : Finset (Fin N)) (R : Run N σ) : Prop :=
  ∀ k ∈ S, ∀ j ∈ S, ∀ s (m : M) s₂, Sends π R k s j m → s + 1 ≤ s₂ → ReceivesAt π R j s₂ →
    ∃ n ≤ s₂, (k, s) ∈ R.deliv j n

/-- The run of Scenarios A and B of the proof of Theorem 4.3 (pp. 305–306): all initial values are
`v`, the processors of `S` take a step at every tick, the processors outside `S` are initially dead
(never take a step), and messages sent from `S` to `S` are delivered in time 1. -/
def IsolatedScenario (π : Protocol N σ M) (S : Finset (Fin N)) (v : Bool) (R : Run N σ) : Prop :=
  IsRun π R ∧ (∀ i, R.val i = v) ∧ (∀ i ∈ S, ∀ n, 1 ≤ n → R.active i n) ∧
    (∀ i, i ∉ S → ∀ n, ¬ R.active i n) ∧ TimeOneWithin π S R

end DLSConsensus.LowerBound


