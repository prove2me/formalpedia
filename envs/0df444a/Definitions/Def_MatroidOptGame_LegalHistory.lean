-- Prove2me | Definitions.Def_MatroidOptGame_LegalHistory
-- name    : MatroidOptGame_LegalHistory
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:53:08.723554+00:00
-- url     : https://prove2.me/theorems/961883fc-69ca-4794-9a6b-883833baac1a
-- title:
--   Legal history of play
-- statement:
--   A history $h$ is **legal** if it arises by legal play from the empty history: at every step the game had not yet ended, and the appended element was a legal move for the player whose turn it was (MAX at even lengths, MIN at odd lengths). MAX moves first.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3 (rounds of the game)

import Mathlib
import Definitions.Def_MatroidOptGame_Ended
import Definitions.Def_MatroidOptGame_LegalMove

namespace MatroidOptGame

/-- `h` is a history of legal play: every move was legal for the player whose turn it was, and
the game had not ended before any move. MAX moves first.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3 (rounds: MAX moves on `M_j`, then MIN on `M′_j`, as long as
the game has not ended; footnote 2 only remarks that the results extend to MIN moving first). -/
inductive LegalHistory {α : Type*} [DecidableEq α] (M : Matroid α) : List α → Prop
  | nil : LegalHistory M []
  | snoc {h : List α} {e : α} :
      LegalHistory M h → ¬ Ended M h → LegalMove M h e → LegalHistory M (h ++ [e])

end MatroidOptGame


