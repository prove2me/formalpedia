-- Prove2me | Definitions.Def_Pr6453_Frames
-- name    : Pr6453_Frames
-- status  : Definition
-- author  : @gustasmickus
-- created : 2026-11-08T20:54:18.127003+00:00
-- url     : https://prove2.me/theorems/65e93635-a3bd-4d14-9c4d-8b6fa7495a97
-- title:
--   PR #6453: the frame step of the replay
-- statement:
--   The frame part of the replay step of PR #6453, isolated.
--
--   Every guard of the replay reads only the frame chart and never the rows, so `frameStep?` is the frame component of a step, returning `none` exactly when a guard fails, and `replayF?` is the fold of a program over it. The point of the definition is the accompanying theorem: legality of a replay is a statement about frames alone. That is what makes a proof of the replay for the 17 926-event word possible at all — the row operations never have to be unfolded.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4: the guarded replay of research/p104-clean-piggyback/construct.py.

/-
# PR #6453: the replay is frame-determined

Every guard of `Pr6453.Replay` reads only the frame chart, never the rows. So the legality of a
replay is a statement about frames alone: this file isolates the frame replay `replayF?` and proves

* `step?_frames` — the frames after a step are the frame step of the frames before it,
* `step?_isSome` — a step succeeds exactly when its frame step does,
* `replay?_isSome` — the same for a whole program.

That is the structural reduction the replay proof rests on: the 17 926 row operations of the word
never have to be unfolded, only the frame chart.
-/
import Definitions.Def_Pr6453_Replay

set_option autoImplicit false


namespace Pr6453

/-! ## The frame step -/

/-- The frame part of one step: `none` exactly when a guard fails. -/
def frameStep? {n : ℕ} (e : Event n) (fr : Fin n → Option ℕ) : Option (Fin n → Option ℕ) :=
  match e with
  | .MOVE c s t => if fr c = some s then some (Function.update fr c (some t)) else none
  | .INIT c f => if fr c = none then some (Function.update fr c (some f)) else none
  | .CLEAR c f => if fr c = some f then some (Function.update fr c none) else none
  | .SCALE c f _ => if fr c = some f then some fr else none
  | .ADD d s _ f => if fr d = some f ∧ fr s = some f then some fr else none

/-- The frame replay of a program. -/
def replayF? {n : ℕ} : List (Event n) → (Fin n → Option ℕ) → Option (Fin n → Option ℕ)
  | [], fr => some fr
  | e :: es, fr => (frameStep? e fr).bind (replayF? es)

end Pr6453


