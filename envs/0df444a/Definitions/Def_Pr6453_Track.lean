-- Prove2me | Definitions.Def_Pr6453_Track
-- name    : Pr6453_Track
-- status  : Definition
-- author  : @gustasmickus
-- created : 2026-11-08T22:01:39.887415+00:00
-- url     : https://prove2.me/theorems/de7c49a5-e484-47f1-876a-896cf0bc757a
-- title:
--   PR #6453: the single-column frame track
-- statement:
--   The single-column frame track of a word: run the events that write the frame of one column, starting from the frame it currently sits at, and see where it lands.
--
--   A frame is written only by the events naming a column — move, initialisation, clear — and each of those acts on its own column alone, so each column carries its own short track through the program. `trackRun` is that track: it skips every event that names another column, and applies the guard of the events that name this one.
--
--   This is the per-stage object the replay of the 17 926-event word is organised around: the construction's stages act on known column sets, each column's frames are read off its own track, and the frame chart is the product of the tracks. The accompanying theorem says the full replay's result at a column is exactly what that column's track computes.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4: the guarded replay of research/p104-clean-piggyback/construct.py.

/-
PR #6453: the single-column frame track.
-/
import Definitions.Def_Pr6453_Locality

set_option autoImplicit false

namespace Pr6453

def trackRun {n : ℕ} (c : Fin n) : List (Event n) → Option ℕ → Option (Option ℕ)
  | [], f => some f
  | e :: es, f =>
      match e with
      | .MOVE c' s t =>
          if c' = c then (if f = some s then trackRun c es (some t) else none) else trackRun c es f
      | .INIT c' fr =>
          if c' = c then (if f = none then trackRun c es (some fr) else none) else trackRun c es f
      | .CLEAR c' fr =>
          if c' = c then (if f = some fr then trackRun c es none else none) else trackRun c es f
      | .SCALE _ _ _ => trackRun c es f
      | .ADD _ _ _ _ => trackRun c es f

end Pr6453


