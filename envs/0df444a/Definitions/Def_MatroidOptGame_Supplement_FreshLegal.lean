-- Prove2me | Definitions.Def_MatroidOptGame_Supplement_FreshLegal
-- name    : MatroidOptGame_Supplement_FreshLegal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:54:26.852179+00:00
-- url     : https://prove2.me/theorems/c82ce815-5d3e-4ce1-8e68-7c254c180ff1
-- title:
--   Legal strategies of the matroid rank maximization game
-- statement:
--   In the **matroid rank maximization game** on a finite ground set $E$ the players alternately secure an element that has not been secured, MAX first, until every element is secured; any element may be taken, loops included. A strategy of the player moving at positions of parity $p$ ($0$ for MAX, $1$ for MIN) is **legal** if at every history without repetitions, of parity $p$, with fewer than $|E|$ moves, it names an element not yet secured.
--
--   **Formalization Note** Legality is required at every repetition-free history, not only those reached in play; a strategy legal along play can be changed elsewhere without changing any play. There is no independence restriction, unlike the base minimization game.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 3, pp.16–17

import Mathlib
import Definitions.Def_MatroidOptGame_Strategy

namespace MatroidOptGame.Supplement

/-- Legality in the matroid rank maximization game for the player moving at positions of parity
`p` (`0`: MAX, who goes first; `1`: MIN): at every duplicate-free history of parity `p` that has
not yet used up the ground set, the strategy secures an element not yet secured. Any element is
allowed, loops included.
Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 3, p.16 ("It's a maximization game, so MAX secures E_M"), p.17 (the dynamic
Lehman move: "secure an arbitrary non-loop element of E^{(j)} (or any element if all are loops)").
**Formalization Note.** Play goes on until every element is secured (`|E|` moves). Legality is
required at every duplicate-free history, not only those reached in play; a strategy legal along
play can be changed off play without changing any play. -/
def FreshLegal {α : Type*} [Fintype α] (p : ℕ) (c : Strategy α) : Prop :=
  ∀ h : List α, h.Nodup → h.length < Fintype.card α → h.length % 2 = p →
    ∃ e, c h = some e ∧ e ∉ h

end MatroidOptGame.Supplement


