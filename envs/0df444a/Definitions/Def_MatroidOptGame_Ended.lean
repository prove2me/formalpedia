-- Prove2me | Definitions.Def_MatroidOptGame_Ended
-- name    : MatroidOptGame_Ended
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:51:58.45927+00:00
-- url     : https://prove2.me/theorems/f73d853f-23df-4b5d-bfb4-ccab6381564a
-- title:
--   End of the game
-- statement:
--   The game **has ended** after history $h$ if either MAX's deletions $C$ include a cut of $M$, or MIN's contractions $S$ form a base of $M$. (The two cannot both hold, since a cut meets every base.)
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3

import Mathlib
import Definitions.Def_MatroidOptGame_minSet
import Definitions.Def_MatroidOptGame_CutDeleted

namespace MatroidOptGame

/-- The game is over after history `h`: MAX's deletions include a cut of `M`, or MIN's
contractions form a base of `M`.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3 ("The game ends if the set C_j … includes a cut in M, or
otherwise if the set S_j … played so far by MIN is a base of M"). -/
def Ended {α : Type*} [DecidableEq α] (M : Matroid α) (h : List α) : Prop :=
  CutDeleted M h ∨ M.IsBase (minSet h : Set α)

end MatroidOptGame


