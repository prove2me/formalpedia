-- Prove2me | Definitions.Def_AvgCompletionSched_BestAlpha_Supplement_Events
-- name    : AvgCompletionSched_BestAlpha_Supplement_Events
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T06:50:56.488582+00:00
-- url     : https://prove2.me/theorems/6528204e-fdd1-418c-b98a-4134bf9870fd
-- title:
--   Counted SRPT event simulation and α-point FIFO reservations
-- statement:
--   The simulation keeps a clock, a chronological external release stream, and the records of released unfinished jobs. A record stores the job's remaining processing and whether its α-point has already been emitted. Dispatch scans only the active records, taking least remaining processing and then least natural job label. Arrivals at a clock value are ingested before dispatch. A dispatched job announces its next α-point or completion; the environment interrupts this timer at an earlier release. Completed records are deleted. The service log records the resulting half-open processing intervals.
--
--   When a job reaches its α-point at time $t$, the simulation emits exactly one FIFO reservation with
--
--   $$S_j=\max\{t,F\},\qquad F\leftarrow S_j+p_j,$$
--
--   where $F$ is the end of the last reserved slot, initially zero. This stores the actual queue's nonpreemptive output even when its machine is still busy. It uses insertion time, not release time. The run with $a=1$ fixes the canonical SRPT service trace; the other runs split that trace additionally at α-points. A preemptive schedule realizes SRPT precisely when its service function equals that trace.
--
--   The finite evaluator allows $6n+1$ event transitions. The theorem must show termination before this fuel is exhausted, feasibility, and prefix consistency across inputs with different future job counts. The fuel is replay bookkeeping, not information a dispatch decision can use. The external stream is an ordered presentation of releases, not offline preprocessing by the policy.
--
--   The counted implementation is a direct scan in the exact arithmetic/comparison model, after the single density sample. Each examined active record is charged eight padded primitive instructions, each event forty scalar/link instructions plus its scans, and output extraction four per examined reservation. The counter accumulates along the executed transition branches and output scans; it is not a polynomial assumed in a definition. Exact real comparisons and arithmetic have unit cost; physical waiting has no computational cost. No finite-bit exact sampling assertion is made.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, DOI 10.1137/S0097539797327180, p. 148, §1 (SRPT); p. 149 (implementation model); p. 155, proof of Theorem 2.8

import Mathlib
import Definitions.Def_AvgCompletionSched_BestAlpha_Model

set_option autoImplicit false

namespace AvgCompletionSched.BestAlpha.Supplement

/-- An active SRPT record. `sent` records whether its alpha event has been emitted. -/
structure Work (n : ℕ) where
  job : Fin n
  left : ℝ
  sent : Bool

/-- Half-open intervals give the simulated preemptive execution, including its endpoints. -/
structure Piece (n : ℕ) where
  job : Fin n
  lo : ℝ
  hi : ℝ

/-- A FIFO reservation, emitted once at the simulated alpha-point. -/
structure Reservation (n : ℕ) where
  job : Fin n
  enqueue : ℝ
  start : ℝ

/-- Finite event-machine state. `arrivals` is the external chronological input stream, not
information available to the dispatch rule. Both logs are stored in reverse order. -/
structure EventState (n : ℕ) where
  clock : ℝ
  arrivals : List (Fin n)
  ready : List (Work n)
  pieces : List (Piece n)
  reservations : List (Reservation n)
  tailFinish : ℝ
  operations : ℕ

variable {n : ℕ}

/-- A direct scan for least remaining work, ties by the fixed job label. The second
component counts padded arithmetic/comparison/read/write instructions: each inspected
record costs eight. No optimum oracle and no sorting oracle are used by dispatch. -/
noncomputable def scanLeast : List (Work n) → Option (Work n) × ℕ
  | [] => (none, 1)
  | x :: xs =>
    let q := scanLeast xs
    match q.1 with
    | none => (some x, q.2 + 8)
    | some y =>
      if x.left < y.left ∨ (x.left = y.left ∧ x.job ≤ y.job) then
        (some x, q.2 + 8)
      else (some y, q.2 + 8)

/-- Update the selected record; delete it precisely when it has finished. Each visited
record executes eight padded primitive instructions. -/
noncomputable def updateWork (j : Fin n) (left : ℝ) (sent : Bool) :
    List (Work n) → List (Work n) × ℕ
  | [] => ([], 1)
  | x :: xs =>
    let q := updateWork j left sent xs
    if x.job = j then
      if 0 < left then (⟨j, left, sent⟩ :: q.1, q.2 + 8) else (q.1, q.2 + 8)
    else (x :: q.1, q.2 + 8)

/-- The environment presents releases chronologically, with label tie-breaking within a
batch. This only represents an input stream; it is not an offline preprocessing step of
the policy. The driver below interrupts the announced internal timer at the next arrival. -/
noncomputable def arrivalStream (I : Instance n) : List (Fin n) :=
  (List.finRange n).mergeSort (fun i j =>
    decide (I.r i < I.r j ∨ (I.r i = I.r j ∧ i ≤ j)))

noncomputable def initialState (I : Instance n) : EventState n :=
  ⟨0, arrivalStream I, [], [], [], 0, 1⟩

def Finished (s : EventState n) : Prop := s.arrivals = [] ∧ s.ready = []

/-- One finite event. Arrivals at the current clock are ingested before dispatch. Otherwise
SRPT announces the next alpha-point/completion timer, and the external driver interrupts
it if a release arrives first. A new alpha event reserves the next FIFO slot at
`max enqueue previousFinish`, not at the job's original release. Forty padded primitive
instructions cover event arithmetic, input/output links and scalar state reads/writes;
the two scans count their own visited records. Unit cost includes exact real arithmetic
and comparisons, as in the scheduling paper, and excludes physical waiting time. -/
noncomputable def eventStep (I : Instance n) (a : ℝ) (s : EventState n) : EventState n := by
  classical
  let ingest := fun (j : Fin n) (rest : List (Fin n)) =>
    { s with
      clock := max s.clock (I.r j)
      arrivals := rest
      ready := ⟨j, I.p j, false⟩ :: s.ready
      operations := s.operations + 40 }
  let arrivalNow := match s.arrivals with
    | [] => false
    | j :: _ => decide (I.r j ≤ s.clock)
  if arrivalNow then
    match s.arrivals with
    | [] => exact s
    | j :: rest => exact ingest j rest
  else
    let q := scanLeast s.ready
    match q.1 with
    | none =>
      match s.arrivals with
      | [] => exact s
      | j :: rest => exact { ingest j rest with operations := s.operations + q.2 + 40 }
    | some x =>
      let delay :=  if x.sent then x.left else x.left - (1 - a) * I.p x.job
      let timer := s.clock + delay
      let next := match s.arrivals with
        | [] => timer
        | j :: _ => min timer (I.r j)
      let left := x.left - (next - s.clock)
      let emit : Bool := !x.sent && decide (left ≤ (1 - a) * I.p x.job)
      let update := updateWork x.job left (x.sent || emit) s.ready
      let start := max next s.tailFinish
      exact { s with
        clock := next
        ready := update.1
        pieces := ⟨x.job, s.clock, next⟩ :: s.pieces
        reservations := if emit then ⟨x.job, next, start⟩ :: s.reservations else s.reservations
        tailFinish := if emit then start + I.p x.job else s.tailFinish
        operations := s.operations + q.2 + update.2 + 40 }

/-- A finite evaluator. Fuel is a termination bound for replaying a finite input, not
advance knowledge supplied to dispatch. Theorem 2.8 proves that no valid input truncates,
and proves prefix consistency even when the number of future jobs changes. -/
noncomputable def replay (I : Instance n) (a : ℝ) : ℕ → EventState n → EventState n
  | 0, s => s
  | k + 1, s => if s.arrivals.isEmpty && s.ready.isEmpty then s else replay I a k (eventStep I a s)

noncomputable def eventRun (I : Instance n) (a : ℝ) : EventState n :=
  replay I a (6 * n + 1) (initialState I)

/-- The simulated service trace. It is empty before time zero and after its last event. -/
noncomputable def eventService (I : Instance n) (a : ℝ) (t : ℝ) : Option (Fin n) :=
  ((eventRun I a).pieces.find? (fun z => decide (z.lo ≤ t ∧ t < z.hi))).map Piece.job

/-- At a=1 the extra alpha event coincides with completion. This pins down one actual SRPT
schedule with fixed labels, rather than an arbitrary preemptive optimum used as an oracle. -/
def IsSRPT {I : Instance n} (P : PreemptiveSchedule I) : Prop :=
  P.σ = eventService I 1

/-- Extract one output start by a counted scan of the emitted reservations. The second
component counts four primitive instructions for each examined output record. -/
noncomputable def scanStart (j : Fin n) : List (Reservation n) → ℝ × ℕ
  | [] => (0, 1)
  | z :: zs => if z.job = j then (z.start, 4) else
      let q := scanStart j zs
      (q.1, q.2 + 4)

/-- Start time emitted by the counted event algorithm. The default only makes this a total
function; the full online theorem asserts unique reservations and feasible outputs for every
valid alpha, so no job in its domain uses the default. -/
noncomputable def eventStart (I : Instance n) (a : ℝ) (j : Fin n) : ℝ :=
  (scanStart j (eventRun I a).reservations).1

/-- Total charged instructions, including extraction of the whole output start vector.
The chronological release stream is supplied by the environment; waiting is not a step. -/
noncomputable def implementationOperations (I : Instance n) (a : ℝ) : ℕ :=
  let s := eventRun I a
  s.operations + ((List.finRange n).map (fun j => (scanStart j s.reservations).2)).sum

end AvgCompletionSched.BestAlpha.Supplement


