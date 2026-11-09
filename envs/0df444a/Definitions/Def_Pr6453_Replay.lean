-- Prove2me | Definitions.Def_Pr6453_Replay
-- name    : Pr6453_Replay
-- status  : Definition
-- author  : @gustasmickus
-- created : 2026-11-08T19:07:19.230901+00:00
-- url     : https://prove2.me/theorems/c2f85e4c-95ac-411b-9043-b80f4a9af611
-- title:
--   PR #6453: the event payloads and the replay condition
-- statement:
--   The event payloads of the PR #6453 word and the replay condition.
--
--   Each event carries a payload: `MOVE col srcFrame dstFrame`, `INIT col frame`, `CLEAR col frame`, `SCALE col frame coef` and `ADD dst src coef frame`, with dyadic rational coefficients. A replay state is a sparse row per column together with the frame at which each column sits; a step applies the row operation to the destination column, guarded by the frame chart. `replay?` folds the program over the guarded step, returning `none` when a guard fails, and `Replay prog st fin` says the program is legal from `st` and ends in `fin`.
--
--   The guards are those of the source's `replay` (`research/p104-clean-piggyback/construct.py`): the destination must sit at the frame the event names, the source of an `ADD` must sit at the same frame, and `INIT` needs a free column. The condition is not proved for the PR #6453 word here — its program has 17 926 events and is not embedded — but it has been checked computationally: the source's replay runs over all 17 926 events, the resulting frames equal the recorded final chart, and every owned row ends empty.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4: WORD.json (program) and native-source.tar research/p104-clean-piggyback/construct.py (replay).

/-
# PR #6453: the event payloads and the replay condition

The word's program is a list of events, and each event carries a payload. Read off `WORD.json`
(the schema `p104-accumulated-block-composition/2`), the five tags carry

* `MOVE col srcFrame dstFrame _`  — `['MOVE', 236, 3, 7, False]`
* `INIT col frame`                — `['INIT', 778, 3]`
* `CLEAR col frame`               — `['CLEAR', 798, 1091]`
* `SCALE col frame coef`          — `['SCALE', 234, '2', 3]`
* `ADD dst src coef frame`        — `['ADD', 230, 224, '2', 3]`

with coefficients dyadic rationals. The state of a replay is a sparse row per column together with
the frame at which each column currently sits, and a step applies the event's row operation to the
destination column, guarded by the frame chart — exactly the guards of the source's `replay`
(`research/p104-clean-piggyback/construct.py`).

The condition is stated as `Replay`: the fold of the program over `step?`, from the initial state,
is defined and ends in the final state. It is *not* proved here for the PR #6453 word: the program
has 17 926 events and is not embedded.
-/
import Definitions.Def_Pr6453_Word
import Mathlib

namespace Pr6453

noncomputable section

/-- The payload of an event of the word. -/
inductive Event (n : ℕ) where
  | MOVE (col : Fin n) (srcFrame dstFrame : ℕ)
  | INIT (col : Fin n) (frame : ℕ)
  | CLEAR (col : Fin n) (frame : ℕ)
  | SCALE (col : Fin n) (frame : ℕ) (coef : ℚ)
  | ADD (dst src : Fin n) (coef : ℚ) (frame : ℕ)

/-- The state of a replay: a sparse row for each column, and the frame (if any) at which it sits. -/
structure State (n : ℕ) where
  rows : Fin n → ℕ →₀ ℚ
  frames : Fin n → Option ℕ

variable {n : ℕ}

/-- One step, with the guards of the source's replay: the destination must sit at the frame the
event names, the source of an `ADD` must sit at the same frame, and `INIT` needs a free column. -/
def step? (e : Event n) (st : State n) : Option (State n) :=
  match e with
  | .MOVE c s t =>
      if st.frames c = some s then some { st with frames := Function.update st.frames c (some t) }
      else none
  | .INIT c f =>
      if st.frames c = none then
        some { rows := Function.update st.rows c 0, frames := Function.update st.frames c (some f) }
      else none
  | .CLEAR c f =>
      if st.frames c = some f then
        some { rows := Function.update st.rows c 0, frames := Function.update st.frames c none }
      else none
  | .SCALE c f q =>
      if st.frames c = some f then
        some { st with rows := Function.update st.rows c (q • st.rows c) }
      else none
  | .ADD d s q f =>
      if st.frames d = some f ∧ st.frames s = some f then
        some { st with rows := Function.update st.rows d (st.rows d + q • st.rows s) }
      else none

/-- The replay of a program from a state: `none` if a guard fails. -/
def replay? : List (Event n) → State n → Option (State n)
  | [], st => some st
  | e :: es, st => (step? e st).bind (replay? es)

/-- **The replay condition**: the program is legal from `st` and ends in `fin`. -/
def Replay (prog : List (Event n)) (st fin : State n) : Prop := replay? prog st = some fin

/-- The initial state of the word: column `i` carries the unit row `e_i` for `i` among the public
inputs and the empty row otherwise, and sits at the frame `initial i`. -/
def initialState (pub owned : ℕ) (h : pub + owned = n) (initial : List ℕ) : State n :=
  { rows := fun i => if _h : (i : ℕ) < pub then Finsupp.single (i : ℕ) 1 else 0
    frames := fun i => if (i : ℕ) < pub then some (initial.getD (i : ℕ) 0) else none }

end
end Pr6453


