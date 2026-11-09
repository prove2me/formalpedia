-- Prove2me | Definitions.Def_MatroidOptGame_Live
-- name    : MatroidOptGame_Live
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:54:09.471577+00:00
-- url     : https://prove2.me/theorems/3470dffb-1418-4ab5-bad0-948c17063d76
-- title:
--   Live position
-- statement:
--   A **live position** is a legal history after which the game has not ended. The player to move is MAX if the history has even length and MIN if it has odd length.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3

import Mathlib
import Definitions.Def_MatroidOptGame_Ended
import Definitions.Def_MatroidOptGame_LegalHistory

namespace MatroidOptGame

/-- A live position: a legal history after which the game has not ended. The player to move is
MAX if `h` has even length and MIN if it has odd length.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3. -/
def Live {α : Type*} [DecidableEq α] (M : Matroid α) (h : List α) : Prop :=
  LegalHistory M h ∧ ¬ Ended M h

end MatroidOptGame


