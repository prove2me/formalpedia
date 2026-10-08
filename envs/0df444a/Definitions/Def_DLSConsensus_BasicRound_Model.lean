-- Prove2me | Definitions.Def_DLSConsensus_BasicRound_Model
-- name    : DLSConsensus_BasicRound_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:19:52.713516+00:00
-- url     : https://prove2.me/theorems/41d4baa6-2ad9-4648-bc77-bdabbb792fdc
-- title:
--   The basic round model (Section 3.1) with omission faults, Algorithm 1 (Section 3.2.1) and the consensus conditions (Section 2.4)
-- statement:
--   This file defines the **basic round model** of Dwork, Lynch and Stockmeyer, the consensus algorithm **Algorithm 1** for fail-stop and omission faults run in it, and the three correctness conditions of a consensus protocol.
--
--   **Processors, rounds, delivery.** There are $N$ processors $p_1,\dots,p_N$, an integer $t$ (the resilience parameter) and an arbitrary value domain $V$; processor $p_i$ starts with an initial value $\mathrm{init}(p_i)\in V$. Computation proceeds in rounds $r=1,2,3,\dots$. In round $r$ every processor sends messages (determined by its state at the start of the round), each message is either delivered in that round or lost, and every processor then applies a state transition to the messages it received. Loss is given by a predicate $\mathrm{deliv}(r,q,p)$: the message from $q$ to $p$ in round $r$ (if any) is delivered iff $\mathrm{deliv}(r,q,p)$ holds. For a set $C$ of processors (the correct ones) and a round $\mathrm{GST}$, the delivery pattern is **allowed** if
--   $$\forall r\ge \mathrm{GST},\ \forall q\in C,\ \forall p\in C:\ \mathrm{deliv}(r,q,p).$$
--   Nothing else is guaranteed: before GST any message may be lost, and messages from or to processors outside $C$ may be lost at any round. A processor's message to itself is treated like any other message.
--
--   **Faults.** Processors outside $C$ run Algorithm 1 as well; their faultiness consists only in lost sends and receptions. This is the **omission** fault model, and it contains the **fail-stop** model (all messages of a processor lost from some round on).
--
--   **Algorithm 1.** Each processor keeps a set $\mathrm{PROPER}$ (initially $\{\mathrm{init}(p)\}$), attached to every message it sends; on receipt it adds every value of every received PROPER set to its own. Each processor holds locks: for each value $v$ at most one lock, with an associated phase number $h$. A value $v$ is **acceptable** to $p$ if $p$ has no lock on any value other than $v$. Phase $k\ge1$ **belongs to** $p_i$ when $k\equiv i\pmod N$. Trying phase $k$ occupies rounds $s=4k-3$, $s+1$, $s+2$; lock-release phase $k$ is round $4k$. With $p_i$ the owner of phase $k$:
--
--   1. Round $s$: every processor sends $p_i$ the list of its acceptable values that are in its PROPER set. Afterwards, the **candidates** of $p_i$ are the values $v$ that appear in the received lists of at least $N-t$ distinct processors (possibly including $p_i$); if there are candidates, $p_i$ proposes one of them, chosen by an arbitrary choice function $\mathrm{pick}(k,\cdot)$; otherwise it proposes nothing.
--   2. Round $s+1$: if $p_i$ proposed $v$, it sends $(\mathrm{lock}\ v,k)$ to all processors, itself included. A processor receiving it locks $v$ with phase $k$ (an earlier lock on $v$ is replaced, locks on other values stay).
--   3. Round $s+2$: each processor that received $(\mathrm{lock}\ v,k)$ sends $(\mathrm{ack},k)$ to $p_i$. If $p_i$ receives acknowledgements from at least $t+1$ processors, $p_i$ **decides** $v$ at phase $k$.
--   4. Round $4k$: every processor sends every processor the set of pairs $(v,h)$ such that it has a lock on $v$ with phase $h$ (even when this set is empty). A processor with a lock on $v$ with phase $h$ releases it if it receives some $(w,h')$ with $w\ne v$ and $h'\ge h$.
--
--   Given $t$, $\mathrm{pick}$, $\mathrm{init}$ and $\mathrm{deliv}$ the run is determined; $\mathrm{exec}(r,p)$ is the state of $p$ after round $r$ ($\mathrm{exec}(0,p)$ is the initial state). A choice function is **admissible** if $\mathrm{pick}(k,S)\in S$ for every nonempty $S$.
--
--   **Correctness conditions** (Section 2.4), for the set $C$:
--
--   1. *Consistency*: no two decisions of processors in $C$ (at any phases, including two decisions of one processor) differ.
--   2. *Termination*: every processor in $C$ decides at some phase.
--   3. *Strong unanimity*: if all $N$ initial values equal $v$, then every decision of a processor in $C$ is $v$.
--
--   These objects are the setting of Lemmas 3.1–3.3 and Theorem 3.1 of the paper.
--
--   **Formalization Note** Processors are `Fin N`, with $p_i$ the processor of index $i-1$, so phase $k$ belongs to the processor of index $p$ iff $k \bmod N = (p+1) \bmod N$. The state also records the owner's current proposal and whether a $(\mathrm{lock}\ v,k)$ message was received in the current phase (to send the acknowledgement). The phase number carried by the paper's messages is implicit: a message is delivered in the round it is sent or never. The paper's "chooses one arbitrarily" becomes the parameter `pick`, quantified universally in every theorem. Locks are `V → Option ℕ` (at most one lock per value). Sets and counts use classical logic; `N - t` is natural-number subtraction, so theorems assume `t ≤ N`. The decision is recorded as the event `DecidesAt p k v`; `LocksAt p k v` means $p$ received $(\mathrm{lock}\ v,k)$ in round $4k-2$.
-- source:
--   Dwork, Lynch, Stockmeyer, Consensus in the presence of partial synchrony, J. ACM 35 (1988), pp. 293–296, Sections 2.2, 2.4, 3.1, 3.2, 3.2.1 (Algorithm 1)

import Mathlib

namespace DLSConsensus.BasicRound

open Classical

/-! # The basic round model and Algorithm 1 of Dwork–Lynch–Stockmeyer (J. ACM 1988)

Processors are `Fin N`; the paper's `p_i` (`i = 1, …, N`) is the processor of index `i - 1`.
Rounds are numbered `1, 2, 3, …`; `exec … r p` is the state of `p` after the computation
subround of round `r`, and `exec … 0 p` is the initial state. Trying phase `k ≥ 1` occupies
rounds `4k - 3, 4k - 2, 4k - 1`, and lock-release phase `k` is round `4k`. -/

/-- Phase `k` belongs to processor `p` (the paper's `p_{p+1}`) iff `k ≡ p + 1 (mod N)`. -/
def Owns {N : ℕ} (p : Fin N) (k : ℕ) : Prop := k % N = (p.val + 1) % N

/-- The phase number of round `r ≥ 1`: rounds `4k - 3, …, 4k` form phase `k`. -/
def phaseOf (r : ℕ) : ℕ := (r + 3) / 4

/-- Local state of a processor: its PROPER set, its locks (`lock v = some h` means a lock on
`v` with associated phase `h`; at most one lock per value), the value it proposed in the
current trying phase (meaningful only for the phase's owner), and whether it received a
`(lock v, k)` message in the second round of the current trying phase. -/
structure PState (V : Type*) where
  proper : Set V
  lock : V → Option ℕ
  proposal : Option V
  ackPending : Prop

/-- Initial state: PROPER is the singleton of the initial value, no locks, no proposal. -/
def initState {V : Type*} (v : V) : PState V :=
  ⟨{v}, fun _ => none, none, False⟩

/-- `v` is acceptable to a processor if it has no lock on any value except possibly `v`. -/
def Acceptable {V : Type*} (s : PState V) (v : V) : Prop :=
  ∀ w, s.lock w ≠ none → w = v

/-- Message contents (the phase number `k` of the paper's messages is the phase of the round in
which the message is sent, since every message is delivered in its own round or lost). -/
inductive Payload (V : Type*)
  /-- `(list, k)`: the sender's acceptable values that are in its PROPER set. -/
  | list (L : Set V)
  /-- `(lock v, k)`. -/
  | lockReq (v : V)
  /-- `(ack, k)`. -/
  | ack
  /-- the lock-release message: all pairs `(v, h)` such that the sender has a lock on `v`
  with phase `h` (sent even when empty). -/
  | locks (S : Set (V × ℕ))

/-- Every message carries the sender's current PROPER set. -/
structure Msg (V : Type*) where
  proper : Set V
  payload : Payload V

/-- The message `q` sends to `p` in round `r`, given `q`'s state at the start of the round
(`none` = no message). -/
noncomputable def send {N : ℕ} {V : Type*} (r : ℕ) (q p : Fin N) (s : PState V) :
    Option (Msg V) :=
  if r % 4 = 1 then
    -- round `4k - 3`: everyone sends its list to the owner of phase `k`
    if Owns p (phaseOf r) then some ⟨s.proper, .list {v | v ∈ s.proper ∧ Acceptable s v}⟩
    else none
  else if r % 4 = 2 then
    -- round `4k - 2`: the owner broadcasts `(lock v, k)` if it proposed `v`
    if Owns q (phaseOf r) then s.proposal.map fun v => ⟨s.proper, .lockReq v⟩ else none
  else if r % 4 = 3 then
    -- round `4k - 1`: whoever received `(lock v, k)` acknowledges to the owner
    if Owns p (phaseOf r) ∧ s.ackPending then some ⟨s.proper, .ack⟩ else none
  else
    -- round `4k`: everyone broadcasts its locks
    some ⟨s.proper, .locks {x | s.lock x.1 = some x.2}⟩

/-- What `p` receives in round `r` from each `q`: `q`'s message if `deliv r q p`, else nothing.
`states` are the states at the start of round `r`. -/
noncomputable def inbox {N : ℕ} {V : Type*} (deliv : ℕ → Fin N → Fin N → Prop)
    (states : Fin N → PState V) (r : ℕ) (p : Fin N) : Fin N → Option (Msg V) :=
  fun q => if deliv r q p then send r q p (states q) else none

/-- The computation subround of round `r` at processor `p`. `pick k S` is the owner's arbitrary
choice among the candidate set `S` at phase `k`. -/
noncomputable def step {N : ℕ} {V : Type*} (t : ℕ) (pick : ℕ → Set V → V) (r : ℕ) (p : Fin N)
    (s : PState V) (box : Fin N → Option (Msg V)) : PState V :=
  let k := phaseOf r
  let proper' : Set V := s.proper ∪ {v | ∃ q m, box q = some m ∧ v ∈ m.proper}
  if r % 4 = 1 then
    let cands : Set V := {v | N - t ≤
      (Finset.univ.filter fun q => ∃ P L, box q = some ⟨P, .list L⟩ ∧ v ∈ L).card}
    { s with proper := proper',
             proposal := if Owns p k ∧ cands.Nonempty then some (pick k cands) else none }
  else if r % 4 = 2 then
    { s with proper := proper',
             lock := fun v => if ∃ q P, box q = some ⟨P, .lockReq v⟩ then some k else s.lock v,
             ackPending := ∃ q P v, box q = some ⟨P, .lockReq v⟩ }
  else if r % 4 = 3 then
    { s with proper := proper' }
  else
    { s with proper := proper',
             lock := fun v => match s.lock v with
               | none => none
               | some h =>
                 if ∃ q P S, box q = some ⟨P, .locks S⟩ ∧ ∃ w h', (w, h') ∈ S ∧ w ≠ v ∧ h ≤ h'
                 then none else some h }

/-- The run of Algorithm 1 determined by `t`, the choice function `pick`, the initial values
`init` and the delivery pattern `deliv r q p` ("the message from `q` to `p` in round `r`
is delivered"). -/
noncomputable def exec {N : ℕ} {V : Type*} (t : ℕ) (pick : ℕ → Set V → V) (init : Fin N → V)
    (deliv : ℕ → Fin N → Fin N → Prop) : ℕ → Fin N → PState V
  | 0 => fun p => initState (init p)
  | r + 1 => fun p =>
      step t pick (r + 1) p (exec t pick init deliv r p)
        (inbox deliv (exec t pick init deliv r) (r + 1) p)

/-- The owner's choice is admissible: it picks an element of every nonempty candidate set. -/
def PickAdmissible {V : Type*} (pick : ℕ → Set V → V) : Prop :=
  ∀ k (S : Set V), S.Nonempty → pick k S ∈ S

/-- The GST constraint of the basic round model: every message sent at a round `r ≥ GST` from a
processor in `C` to a processor in `C` (itself included) is delivered. -/
def DelivOK {N : ℕ} (C : Finset (Fin N)) (GST : ℕ) (deliv : ℕ → Fin N → Fin N → Prop) : Prop :=
  ∀ r, GST ≤ r → ∀ q ∈ C, ∀ p ∈ C, deliv r q p

/-- The processors that lock `v` at phase `k`: those receiving `(lock v, k)` in round `4k - 2`. -/
noncomputable def Lockers {N : ℕ} {V : Type*} (t : ℕ) (pick : ℕ → Set V → V) (init : Fin N → V)
    (deliv : ℕ → Fin N → Fin N → Prop) (k : ℕ) (v : V) : Finset (Fin N) :=
  Finset.univ.filter fun p =>
    ∃ q P, inbox deliv (exec t pick init deliv (4 * k - 3)) (4 * k - 2) p q = some ⟨P, .lockReq v⟩

/-- `p` locks `v` at phase `k ≥ 1`. -/
def LocksAt {N : ℕ} {V : Type*} (t : ℕ) (pick : ℕ → Set V → V) (init : Fin N → V)
    (deliv : ℕ → Fin N → Fin N → Prop) (p : Fin N) (k : ℕ) (v : V) : Prop :=
  1 ≤ k ∧ p ∈ Lockers t pick init deliv k v

/-- The processors from which `p` receives `(ack, k)` in round `4k - 1`. -/
noncomputable def Ackers {N : ℕ} {V : Type*} (t : ℕ) (pick : ℕ → Set V → V) (init : Fin N → V)
    (deliv : ℕ → Fin N → Fin N → Prop) (p : Fin N) (k : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun q =>
    ∃ P, inbox deliv (exec t pick init deliv (4 * k - 2)) (4 * k - 1) p q = some ⟨P, .ack⟩

/-- `p` decides `v` at phase `k ≥ 1`: `p` owns phase `k`, proposed `v` just after round
`4k - 3`, and received `(ack, k)` from at least `t + 1` processors in round `4k - 1`. -/
def DecidesAt {N : ℕ} {V : Type*} (t : ℕ) (pick : ℕ → Set V → V) (init : Fin N → V)
    (deliv : ℕ → Fin N → Fin N → Prop) (p : Fin N) (k : ℕ) (v : V) : Prop :=
  1 ≤ k ∧ Owns p k ∧ (exec t pick init deliv (4 * k - 3) p).proposal = some v ∧
    t + 1 ≤ (Ackers t pick init deliv p k).card

/-- Consistency (Section 2.4): no two decisions of processors in `C` differ. -/
def Consistency {N : ℕ} {V : Type*} (t : ℕ) (pick : ℕ → Set V → V) (init : Fin N → V)
    (deliv : ℕ → Fin N → Fin N → Prop) (C : Finset (Fin N)) : Prop :=
  ∀ p ∈ C, ∀ q ∈ C, ∀ (k k' : ℕ) (v w : V),
    DecidesAt t pick init deliv p k v → DecidesAt t pick init deliv q k' w → v = w

/-- Termination (Section 2.4; runs of the basic model are infinite): every processor in `C`
decides. -/
def Termination {N : ℕ} {V : Type*} (t : ℕ) (pick : ℕ → Set V → V) (init : Fin N → V)
    (deliv : ℕ → Fin N → Fin N → Prop) (C : Finset (Fin N)) : Prop :=
  ∀ p ∈ C, ∃ (k : ℕ) (v : V), DecidesAt t pick init deliv p k v

/-- Strong unanimity (Section 2.4): if all `N` initial values are `v`, every decision of a
processor in `C` is `v`. -/
def StrongUnanimity {N : ℕ} {V : Type*} (t : ℕ) (pick : ℕ → Set V → V) (init : Fin N → V)
    (deliv : ℕ → Fin N → Fin N → Prop) (C : Finset (Fin N)) : Prop :=
  ∀ v : V, (∀ q, init q = v) → ∀ p ∈ C, ∀ (k : ℕ) (w : V),
    DecidesAt t pick init deliv p k w → w = v

end DLSConsensus.BasicRound


