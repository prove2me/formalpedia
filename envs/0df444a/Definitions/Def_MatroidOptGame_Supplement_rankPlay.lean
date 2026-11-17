-- Prove2me | Definitions.Def_MatroidOptGame_Supplement_rankPlay
-- name    : MatroidOptGame_Supplement_rankPlay
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:54:46.64338+00:00
-- url     : https://prove2.me/theorems/3facb496-7e4f-4972-b968-7e13c045ea48
-- title:
--   Play of the matroid rank maximization game
-- statement:
--   The play of a MAX strategy $c$ against a MIN strategy $s$ in the matroid rank maximization game: starting from the empty history, MAX (at even history lengths) and MIN (at odd lengths) alternately append their move, for $|E|$ moves, with no early end. MAX's secured set $E_M$ is the set of moves at even positions (the published `maxSet`), and MAX's payoff is $r_M(E_M)$.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 3, p.16

import Mathlib
import Definitions.Def_MatroidOptGame_Strategy

namespace MatroidOptGame.Supplement

/-- The play of the matroid rank maximization game between MAX strategy `c` (moving first, at even
history lengths) and MIN strategy `s` (odd lengths): `|E|` moves, each appended to the history,
with no early end. MAX's secured set `E_M` is `maxSet` of the play.
Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 3, p.16 (players alternately secure elements; "MAX secures E_M. MAX's payoff,
which MIN tries to minimize, is r_M(E_M)"; Theorem 15: "Assume MAX goes first").
**Formalization Note.** If a strategy returns `none` the history stays put; legal strategies
(`Supplement.FreshLegal`) never do so before every element is secured. -/
def rankPlay {α : Type*} [Fintype α] (c s : Strategy α) : List α :=
  (fun h : List α =>
      match (if h.length % 2 = 0 then c h else s h) with
      | some e => h ++ [e]
      | none => h)^[Fintype.card α] []

end MatroidOptGame.Supplement


