-- Prove2me | Definitions.Def_EulerianLE_Run
-- name    : EulerianLE_Run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:56:07.683555+00:00
-- url     : https://prove2.me/theorems/70c5b96d-2cfe-4193-b5e1-667f343be951
-- title:
--   Configurations, gated fair executions, observations and traces
-- statement:
--   A **configuration** records, for every node, whether it is asleep, running (with its program state) or completed (with its output); for every port $p$, the pulses in transit to $p$ and those queued at $p$, oldest first; and the numbers $\sigma_p$ and $\rho_p$ of pulses sent through and consumed at $p$. Every pulse carries a phase label used only for the analysis.
--
--   An **execution** starts with every node asleep and no pulse anywhere and proceeds by events: a *wake-up* of a node, the *delivery* of the oldest pulse in transit to a port (channels are FIFO), or an *operation* of an awake node. Wake-ups and deliveries occur only when no node can execute an instruction, since local computation takes no time. An execution stops only when no event can occur. It is **fair** if every node eventually wakes up and every pulse in transit is eventually delivered. A pulse delivered to a completed node stays queued.
--
--   A successful test for at least $k$ pulses **observes** the first $k$ pulses at the selected port, a consumption observes the consumed pulse, an unsuccessful test observes nothing. The module also defines: completion and the completion step of a node; the total number of pulses sent; **quiescence** of an execution (when a node completes, every port $p$ of it has consumed as many pulses as are ever sent through $\mathrm{link}(p)$); and the traces used to compare executions (the scheduler events, the visible operations with a view of the node's state, the local trace of a node).
--
--   **Formalization Note** A scheduler of the paper with its execution is a fair run; fairness does not force progress, so a run in which some node blocks forever is fair.
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), §2, p.8 (PDF p.10): executions, schedulers, FIFO channels, observation, termination; §3.2, p.10 (no delivery between operations at the same time)

import Mathlib
import Definitions.Def_EulerianLE_Network
import Definitions.Def_EulerianLE_NodeProg

namespace EulerianLE

/-- The status of a node in an execution. -/
inductive Status (σ Out : Type) : Type
  | asleep
  | running (s : σ)
  | completed (out : Out)

/-- `true` when the status is `completed`. -/
def Status.isDone {σ Out : Type} : Status σ Out → Bool
  | .completed _ => true
  | _ => false

/-- The phase label of a pulse in a composition `(A, B)`: "A pulse sent by a node while it executes A
is called an A-pulse; B-pulses are defined in the same way. These phase labels are for analysis only
and are not accessible to the nodes" (Frei, Gelles, Ghazy, Nolin, STOC 2027 submission (manuscript
sha256 90954a93…), §3.1, p.8). -/
inductive Phase : Type
  | first
  | second
  deriving DecidableEq

variable {G : Network} {Out : G.V → Type}

/-- A configuration of an execution of the node programs `P`.

**Formalization Note.** `transit p` and `queue p` list the labels of the pulses on their way **to**
port `p` and of those queued at `p`, oldest first: channels are FIFO and "queued pulses are consumed
in delivery order" (§2, p.8). `sent p` and `consumed p` count σ and ρ at `p` since the execution
started. Programs never read `transit`, `queue` or the labels; a test reads queue lengths only. -/
structure Config (G : Network) {Out : G.V → Type} (P : ∀ v, NodeProg (G.deg v) (Out v)) where
  status : ∀ v, Status (P v).State (Out v)
  transit : G.Port → List Phase
  queue : G.Port → List Phase
  sent : G.Port → ℕ
  consumed : G.Port → ℕ

/-- The start of a standalone execution: every node asleep, "no pulse in transit and empty queues"
(§2, p.8). -/
def Config.init (P : ∀ v, NodeProg (G.deg v) (Out v)) : Config G P where
  status := fun _ => .asleep
  transit := fun _ => []
  queue := fun _ => []
  sent := fun _ => 0
  consumed := fun _ => 0

/-- The events of an execution: a `WakeUp` of a node, a `PulseDeliver` at a port, and an operation
(one instruction) of a node. -/
inductive Event (G : Network) : Type
  | wake (v : G.V)
  | deliver (p : G.Port)
  | op (v : G.V)

/-- The phase label a program gives the pulses it sends, as a function of its state. -/
abbrev Tag (P : ∀ v, NodeProg (G.deg v) (Out v)) : Type := ∀ v, (P v).State → Phase

/-- The labels of a standalone execution, where they play no role. -/
def stdTag (P : ∀ v, NodeProg (G.deg v) (Out v)) : Tag P := fun _ _ => .first

variable {P : ∀ v, NodeProg (G.deg v) (Out v)}

/-- The queue lengths at the ports of `v`. -/
def Config.lens (c : Config G P) (v : G.V) (i : Fin (G.deg v)) : ℕ := (c.queue ⟨v, i⟩).length

/-- `v` is awake and its next instruction can be executed (a test can when a guard succeeds or it does
not block). -/
def Config.enabled (c : Config G P) (v : G.V) : Bool :=
  match c.status v with
  | .running s =>
    match (P v).step s with
    | .test gs fl _ => (fireFrom (c.lens v) gs 0).isSome || fl.isSome
    | _ => true
  | _ => false

/-- No node can execute an instruction. -/
def Config.Quiet (c : Config G P) : Prop := ∀ v, c.enabled v = false

instance (c : Config G P) : Decidable c.Quiet := by unfold Config.Quiet; infer_instance

/-- The configuration after an event, if the event can occur. A send appends the sender's label to
the channel; a delivery moves the oldest pulse of a channel to the end of the port's queue; a
successful `take` guard removes the oldest pulse of the selected queue.

**Formalization Note (the gate).** `wake` and `deliver` require `Quiet`. This is "Local computation
takes no time" (§2, p.8) and "No delivery occurs between operations that a node performs at the same
time" (§3.2, p.10): scheduler events occur only between bursts of operations. A pulse delivered to a
completed node stays in its queue. -/
def Config.step (tag : Tag P) (c : Config G P) : Event G → Option (Config G P)
  | .wake v =>
    match c.status v with
    | .asleep =>
      if c.Quiet then some { c with status := Function.update c.status v (.running (P v).init) }
      else none
    | _ => none
  | .deliver p =>
    match c.transit p with
    | [] => none
    | h :: tl =>
      if c.Quiet then
        some { c with
          transit := Function.update c.transit p tl
          queue := Function.update c.queue p (c.queue p ++ [h]) }
      else none
  | .op v =>
    match c.status v with
    | .running s =>
      match (P v).step s with
      | .send i n =>
        some { c with
          status := Function.update c.status v (.running n)
          sent := Function.update c.sent ⟨v, i⟩ (c.sent ⟨v, i⟩ + 1)
          transit := Function.update c.transit (G.link ⟨v, i⟩)
            (c.transit (G.link ⟨v, i⟩) ++ [tag v s]) }
      | .tau n => some { c with status := Function.update c.status v (.running n) }
      | .complete o => some { c with status := Function.update c.status v (.completed o) }
      | .test gs fl sc =>
        match fireFrom (c.lens v) gs 0 with
        | some (n, g, p) =>
          if g.take then
            some { c with
              status := Function.update c.status v (.running (sc n p))
              queue := Function.update c.queue ⟨v, p⟩ (c.queue ⟨v, p⟩).tail
              consumed := Function.update c.consumed ⟨v, p⟩ (c.consumed ⟨v, p⟩ + 1) }
          else
            some { c with status := Function.update c.status v (.running (sc n p)) }
        | none =>
          match fl with
          | some s' => some { c with status := Function.update c.status v (.running s') }
          | none => none
    | _ => none

/-- The labels of the pulses that the operation of `v` at `c` observes: "A successful test for at least
k pulses at a set of ports selects the smallest port of the set at which at least k pulses are waiting
and observes the first k pulses there. Consuming a pulse observes it as well" (§2, p.8); an
unsuccessful test observes none. -/
def Config.observed (c : Config G P) (v : G.V) : List Phase :=
  match c.status v with
  | .running s =>
    match (P v).step s with
    | .test gs _ _ =>
      match fireFrom (c.lens v) gs 0 with
      | some (_, g, p) => (c.queue ⟨v, p⟩).take (max g.need 1)
      | none => []
    | _ => []
  | _ => []

/-- An execution (a standalone execution under a scheduler, §2, p.8): a sequence of configurations from
the start, each obtained from the previous one by the event `ev t`; it stops (stutters, `ev t = none`)
only when no event can occur. -/
structure Run (P : ∀ v, NodeProg (G.deg v) (Out v)) (tag : Tag P) where
  cfg : ℕ → Config G P
  ev : ℕ → Option (Event G)
  start : cfg 0 = Config.init P
  next : ∀ t, match ev t with
    | some e => (cfg t).step tag e = some (cfg (t + 1))
    | none => cfg (t + 1) = cfg t ∧ ∀ e, (cfg t).step tag e = none

variable {tag : Tag P}

/-- The scheduler's fairness: "Each of these events occurs after finitely many others, so every node
eventually wakes up and every sent pulse is eventually delivered" (§2, p.8). Since channels are FIFO,
"a pulse in transit to `p` is eventually followed by a delivery at `p`" for every time gives every
pulse its delivery.

**Formalization Note.** Fairness does not force progress: a run in which some node blocks forever is
fair, so "every node completes" is a real claim. -/
def IsFair (ρ : Run P tag) : Prop :=
  (∀ v, ∃ t, ¬ (ρ.cfg t).status v = .asleep) ∧
  ∀ t p, (ρ.cfg t).transit p ≠ [] → ∃ t', t ≤ t' ∧ ρ.ev t' = some (.deliver p)

/-- `v` eventually completes with output `o`. -/
def Run.CompletesWith (ρ : Run P tag) (v : G.V) (o : Out v) : Prop :=
  ∃ t, (ρ.cfg t).status v = .completed o

/-- Every node completes, with the outputs `y` (the output tuple of the execution, §3.1, p.9). -/
def Run.Outputs (ρ : Run P tag) (y : ∀ v, Out v) : Prop := ∀ v, ρ.CompletesWith v (y v)

/-- `v` completes at step `t`: it is not completed at time `t` and is completed at time `t + 1`. -/
def Run.CompletesAt (ρ : Run P tag) (v : G.V) (t : ℕ) : Prop :=
  ((ρ.cfg t).status v).isDone = false ∧ ((ρ.cfg (t + 1)).status v).isDone = true

/-- The total number of pulses sent by time `t`. -/
def Run.totalSent (ρ : Run P tag) (t : ℕ) : ℕ := ∑ p, (ρ.cfg t).sent p

/-- The execution sends exactly `N` pulses in total. -/
def Run.SendsExactly (ρ : Run P tag) (N : ℕ) : Prop :=
  ∃ t, ∀ t', t ≤ t' → ρ.totalSent t' = N

/-- Quiescence of one execution: "every pulse sent to a node is consumed before that node completes"
(§2, p.8): when `v` completes, every port `p` of `v` has consumed as many pulses as are ever sent
through the port `link p` at the other end of its edge. -/
def Run.Quiescent (ρ : Run P tag) : Prop :=
  ∀ v t, ρ.CompletesAt v t → ∀ (i : Fin (G.deg v)) t',
    (ρ.cfg t').sent (G.link ⟨v, i⟩) ≤ (ρ.cfg (t + 1)).consumed ⟨v, i⟩

/-- The number of pulses delivered at `p` so far: those still queued and those consumed. -/
def Config.delivered (c : Config G P) (p : G.Port) : ℕ := (c.queue p).length + c.consumed p

/-- The externally visible operation of a node, for comparing two executions: a send through a port,
a consumption at a port, a successful queue test observing `k` pulses at a port, or completion. -/
inductive Act (deg : ℕ) : Type
  | send (i : Fin deg)
  | consume (i : Fin deg)
  | observe (i : Fin deg) (k : ℕ)
  | complete

/-- The visible operation that `v` performs at `c`, if any (local computation and unsuccessful
non-blocking tests are invisible). -/
def Config.act (c : Config G P) (v : G.V) : Option (Act (G.deg v)) :=
  match c.status v with
  | .running s =>
    match (P v).step s with
    | .send i _ => some (.send i)
    | .tau _ => none
    | .complete _ => some .complete
    | .test gs _ _ =>
      match fireFrom (c.lens v) gs 0 with
      | some (_, g, p) => if g.take then some (.consume p) else some (.observe p (max g.need 1))
      | none => none
  | _ => none

/-- An entry of the external trace of an execution: a scheduler event, or a visible operation of a
node together with a view `α v` of the node's local state when it performs the operation. -/
inductive ExtEv (G : Network) (α : G.V → Type) : Type
  | wake (v : G.V)
  | deliver (p : G.Port)
  | act (v : G.V) (a : Act (G.deg v)) (view : α v)

/-- The external trace up to time `t`, with local states seen through `view`. -/
def Run.extTrace {α : G.V → Type} (ρ : Run P tag) (view : ∀ v, (P v).State → α v) (t : ℕ) :
    List (ExtEv G α) :=
  (List.range t).filterMap fun k =>
    match ρ.ev k with
    | some (.wake v) => some (.wake v)
    | some (.deliver p) => some (.deliver p)
    | some (.op v) =>
      match (ρ.cfg k).status v, (ρ.cfg k).act v with
      | .running s, some a => some (.act v a (view v s))
      | _, _ => none
    | none => none

/-- The scheduler's part of an execution up to time `t`: its wake-ups and deliveries, in order. -/
def Run.schedTrace (ρ : Run P tag) (t : ℕ) : List (Event G) :=
  (List.range t).filterMap fun k =>
    match ρ.ev k with
    | some (.op _) => none
    | e => e

/-- Two growing traces describe the same (finite or infinite) sequence: they have the same finite
prefixes. -/
def SameSeq {α : Type} (f g : ℕ → List α) : Prop :=
  (∀ t, ∃ t', f t = g t') ∧ (∀ t', ∃ t, f t = g t')

/-- The local trace of `v` up to time `t`: for each wake-up of `v` and each operation of `v`, in order,
the visible operation (if any) and the status of `v` right after it. -/
def Run.localTrace (ρ : Run P tag) (v : G.V) (t : ℕ) :
    List (Option (Act (G.deg v)) × Status (P v).State (Out v)) :=
  (List.range t).filterMap fun k =>
    match ρ.ev k with
    | some (.wake w) => if w = v then some (none, (ρ.cfg (k + 1)).status v) else none
    | some (.op w) => if w = v then some ((ρ.cfg k).act v, (ρ.cfg (k + 1)).status v) else none
    | _ => none

end EulerianLE


