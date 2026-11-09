-- Prove2me | Definitions.Def_MatroidOptGame_playout
-- name    : MatroidOptGame_playout
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:53:29.940188+00:00
-- url     : https://prove2.me/theorems/7f09e733-3259-4e46-85d6-05a0c44aedd4
-- title:
--   The play of two strategies
-- statement:
--   Given a MAX strategy $c$ and a MIN strategy $s$, the **play** is the history obtained from the empty history by letting the player to move (MAX at even lengths, MIN at odd lengths) append its chosen element, as long as the game has not ended. At most $|E|$ moves are made: legal play never repeats an element, and once every element is played the game has ended.
--
--   **Formalization Note** The play is the $|E|$-fold iterate of one round of this rule; if a strategy names no move the history stays put (legal strategies never do so at a live position).
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3

import Mathlib
import Definitions.Def_MatroidOptGame_Ended
import Definitions.Def_MatroidOptGame_Strategy

namespace MatroidOptGame

open Classical in
/-- The play of MAX strategy `c` against MIN strategy `s`: starting from the empty history, as
long as the game has not ended, the player to move (MAX on even length, MIN on odd length)
appends its move. `Fintype.card α` rounds suffice: legal play never repeats an element, and once
every element has been played the game has ended.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3 (the rounds of the game).

**Formalization Note.** If a strategy returns `none` the history stays put; legal strategies never
do so at a live position. -/
noncomputable def playout {α : Type*} [Fintype α] [DecidableEq α] (M : Matroid α)
    (c s : Strategy α) : List α :=
  (fun h : List α =>
      if Ended M h then h
      else match (if h.length % 2 = 0 then c h else s h) with
        | some e => h ++ [e]
        | none => h)^[Fintype.card α] []

end MatroidOptGame


