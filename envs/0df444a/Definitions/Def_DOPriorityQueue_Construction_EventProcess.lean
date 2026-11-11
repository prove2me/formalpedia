-- Prove2me | Definitions.Def_DOPriorityQueue_Construction_EventProcess
-- name    : DOPriorityQueue_Construction_EventProcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:03:14.671878+00:00
-- url     : https://prove2.me/theorems/f76c92b2-311b-4a10-80c0-a41647f62e12
-- title:
--   §§4.2 and 5.1 — event index, insertion counts, extraction counts and live prefix counts
-- statement:
--   An event sequence of the stable priority queue is a list whose entries are real calls, $\operatorname{Insert}(p,v)$ or $\operatorname{ExtractMin}()$, or auxiliary events (replacements of committed segments, Section 4.2), which change no record and are not calls. Call indices are one-based and count only real calls. Event $t$ is the state after the first $t$ entries, so events are indexed $0,\ldots,n$.
--
--   A record inserted by call $i$ with priority $p$ has key $(p,i)$, ordered lexicographically; a threshold is any pair $x$. For an event sequence and $0\le t$:
--
--   - $A_t(x)$ counts all original records inserted by event $t$ with key at most $x$, including records already extracted;
--   - $N_t$ counts all extraction calls through event $t$, including empty ones;
--   - $Q_t(x)$ counts the records still live in the stable queue after event $t$ with key at most $x$.
--
--   All three start at $0$. The running minimum of an integer sequence is
--   $$\min_{0\le u\le t}X_u.$$
-- source:
--   Zimai Guo, Cheng Hong, Zhechen Li, STOC 2027 submission #538 (October 2026), p. 10, §4.2; pp. 20–21, §5.1

import Definitions.Def_DOPriorityQueue_Construction_Queue

set_option autoImplicit false

namespace DOPriorityQueue.Construction

/-- Section 4.2 event index: `some op` is a real call of the queue, `none` is an
auxiliary event (a replacement of committed segments), which changes no record. -/
abbrev Event (Ball : Type) := Option (Operation Ball)

/-- A key `(p, i)` (priority, one-based insertion-call index) is at most the
threshold `x` in the lexicographic order of Section 2. -/
def keyAtMost (k x : ℕ × ℕ) : Prop :=
  k.1 < x.1 ∨ (k.1 = x.1 ∧ k.2 ≤ x.2)

instance (k x : ℕ × ℕ) : Decidable (keyAtMost k x) :=
  inferInstanceAs (Decidable (k.1 < x.1 ∨ (k.1 = x.1 ∧ k.2 ≤ x.2)))

/-- The stable queue's live records after a list of events, starting from call
index `i` and state `q`. Auxiliary events leave the state and call index unchanged. -/
def stateAfter {Ball : Type} : ℕ → List (Record Ball) → List (Event Ball) → List (Record Ball)
  | _, q, [] => q
  | i, q, none :: rest => stateAfter i q rest
  | i, q, some op :: rest => stateAfter (i + 1) (queueStep i q op).1 rest

/-- Keys of all original insertions among the events, in order, with call index from `i`. -/
def insertKeys {Ball : Type} : ℕ → List (Event Ball) → List (ℕ × ℕ)
  | _, [] => []
  | i, none :: rest => insertKeys i rest
  | i, some (.insert p _) :: rest => (p, i) :: insertKeys (i + 1) rest
  | i, some .extractMin :: rest => insertKeys (i + 1) rest

/-- `A_t(x)`: original records inserted by event `t` with key at most `x`,
including records already extracted. -/
def insertedAtMost {Ball : Type} (events : List (Event Ball)) (t : ℕ) (x : ℕ × ℕ) : ℕ :=
  ((insertKeys 1 (events.take t)).filter (fun k => decide (keyAtMost k x))).length

/-- `N_t`: all extraction calls through event `t`, including empty ones. -/
def extractionCount {Ball : Type} (events : List (Event Ball)) (t : ℕ) : ℕ :=
  (events.take t).countP (fun e => match e with
    | some .extractMin => true
    | _ => false)

/-- `Q_t(x)`: currently live records after event `t` with key at most `x`. -/
def liveAtMost {Ball : Type} (events : List (Event Ball)) (t : ℕ) (x : ℕ × ℕ) : ℕ :=
  ((stateAfter 1 [] (events.take t)).filter
    (fun r => decide (keyAtMost (r.priority, r.insertedAt) x))).length

/-- The running minimum `min_{0 ≤ u ≤ t} X u` of an integer sequence. -/
def runningMin (X : ℕ → ℤ) (t : ℕ) : ℤ :=
  (Finset.range (t + 1)).inf' (by simp) X

end DOPriorityQueue.Construction


