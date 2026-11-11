-- Prove2me | Definitions.Def_DOPriorityQueue_Construction_Queue
-- name    : DOPriorityQueue_Construction_Queue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:02:16.026944+00:00
-- url     : https://prove2.me/theorems/62035b9a-a72f-49bd-af64-6104845b9c2d
-- title:
--   §2 — stable priority queues and the fixed-pattern wrapper
-- statement:
--   An operation is an insertion of an integer priority and an opaque payload, or an extraction. The initially empty queue orders records lexicographically by priority and the one-based index of their insertion call. Extraction returns the minimum priority and whole payload, or an empty answer. Insertion acknowledgments and empty extraction answers are distinct.
--
--   For public horizon $T$ and integer domain $[U]=\{1,\ldots,U\}$, an admissible history has length at most $T$ and every inserted priority belongs to $[U]$. Neighbors have equal length and differ in at most one complete operation. The insertion-only relation additionally fixes the type at every position.
--
--   The wrapper encodes round $t$ by two insertions followed by extraction. An insertion supplies $(T+p,\operatorname{real}(v))$ and guard priority $t$; an extraction supplies dummy priorities $T+U+2t$ and $T+U+2t+1$. Tags preserve the whole opaque payload.
--
--   These are mathematical input, answer and history transformations. The list-based queue specification is not asserted to be an efficient implementation. The wrapper program, its answer translation and its overhead are not defined here.
-- source:
--   Zimai Guo, Cheng Hong, Zhechen Li, STOC 2027 submission #538 (October 2026), pp. 2–4, §2; p. 20, §4.4

import Mathlib

set_option autoImplicit false

namespace DOPriorityQueue.Construction

/-- Section 2: the payload type is opaque to the queue specification. -/
inductive Operation (Ball : Type) where
  | insert (priority : ℕ) (payload : Ball)
  | extractMin
  deriving DecidableEq

/-- A stored original insertion; the timestamp is its one-based call index. -/
structure Record (Ball : Type) where
  priority : ℕ
  insertedAt : ℕ
  payload : Ball
  deriving DecidableEq

/-- Distinguishes the acknowledgment of an insertion from an empty extraction. -/
inductive Answer (Ball : Type) where
  | inserted
  | extracted (value : Option (ℕ × Ball))
  deriving DecidableEq

/-- Stable order is priority first, then insertion-call index. -/
def keyLE {Ball : Type} (a b : Record Ball) : Prop :=
  a.priority < b.priority ∨
    (a.priority = b.priority ∧ a.insertedAt ≤ b.insertedAt)

instance {Ball : Type} : DecidableRel (@keyLE Ball) := fun a b =>
  inferInstanceAs (Decidable (a.priority < b.priority ∨
    (a.priority = b.priority ∧ a.insertedAt ≤ b.insertedAt)))

/-- This list is a mathematical specification, not a RAM implementation. -/
def queueStep {Ball : Type} (callIndex : ℕ) (q : List (Record Ball)) :
    Operation Ball → List (Record Ball) × Answer Ball
  | .insert p v =>
    (List.orderedInsert keyLE ⟨p, callIndex, v⟩ q, .inserted)
  | .extractMin => match q with
    | [] => ([], .extracted none)
    | r :: rest => (rest, .extracted (some (r.priority, r.payload)))

/-- The unique answers from the initially empty, stable priority queue. -/
def queueRun {Ball : Type} :
    ℕ → List (Record Ball) → List (Operation Ball) → List (Answer Ball)
  | _, _, [] => []
  | i, q, op :: rest =>
    let result := queueStep i q op
    result.2 :: queueRun (i + 1) result.1 rest

def exactAnswers {Ball : Type} (history : List (Operation Ball)) : List (Answer Ball) :=
  queueRun 1 [] history

/-- Domain [U] means 1 through U. Empty extractions are always admissible. -/
def validHistory {Ball : Type} (T U : ℕ) (history : List (Operation Ball)) : Prop :=
  history.length ≤ T ∧ ∀ op ∈ history, match op with
    | .insert p _ => 1 ≤ p ∧ p ≤ U
    | .extractMin => True

/-- At most one complete operation changes, including its code and payload. -/
def neighbors {Ball : Type} (h h' : List (Operation Ball)) : Prop :=
  h.length = h'.length ∧
    ∃ i : ℕ, ∀ j : ℕ, j ≠ i → h[j]? = h'[j]?

/-- The public-type core protects insertion-field replacement only. -/
def insertionNeighbors {Ball : Type} (h h' : List (Operation Ball)) : Prop :=
  neighbors h h' ∧ ∀ j : ℕ, match h[j]?, h'[j]? with
    | some (.insert _ _), some (.insert _ _) => True
    | some .extractMin, some .extractMin => True
    | none, none => True
    | _, _ => False

/-- The wrapper inserts whole opaque balls; tags are separate metadata. -/
inductive WrappedBall (Ball : Type) where
  | real (value : Ball)
  | guard
  | dummy
  deriving DecidableEq

/-- Section 4.4, exactly two insertions and one extraction per source call. -/
def wrapOperation {Ball : Type} (T U round : ℕ) :
    Operation Ball → List (Operation (WrappedBall Ball))
  | .insert p v =>
    [.insert (T + p) (.real v), .insert round .guard, .extractMin]
  | .extractMin =>
    [.insert (T + U + 2 * round) .dummy,
     .insert (T + U + 2 * round + 1) .dummy, .extractMin]

def wrapHistoryFrom {Ball : Type} (T U : ℕ) :
    ℕ → List (Operation Ball) → List (Operation (WrappedBall Ball))
  | _, [] => []
  | round, op :: rest =>
    wrapOperation T U round op ++ wrapHistoryFrom T U (round + 1) rest

def wrapHistory {Ball : Type} (T U : ℕ) (h : List (Operation Ball)) :
    List (Operation (WrappedBall Ball)) := wrapHistoryFrom T U 1 h

end DOPriorityQueue.Construction


