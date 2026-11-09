-- Prove2me | Definitions.Def_MatroidOptGame_Strategy
-- name    : MatroidOptGame_Strategy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:49:49.922771+00:00
-- url     : https://prove2.me/theorems/1b3f99a2-f9f5-4df4-a846-6745a9e15bf1
-- title:
--   Pure strategy on histories
-- statement:
--   A **pure strategy** is a function assigning to every history an (optional) next move.
--
--   The paper describes pure strategies as functions mapping every positive-rank minor $M'$ of $M$ to an element of its ground set. Here strategies are functions of the full history of moves, the standard pure strategies of a finite perfect-information game.
--
--   **Formalization Note** A minor $M/S\setminus C$ forgets which removed elements were deleted and which contracted, while the paper's efficient strategies (Lemmas 5–7) are described along the play; both strategy spaces give the same value by backward induction. The next move is optional so that the strategy type is nonempty even on an empty ground set; legality demands an actual move wherever the player must move.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3

import Mathlib

namespace MatroidOptGame

/-- A pure strategy: a function from histories to an optional next move.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3 ("the set of pure strategies can be expressed as the set of all
functions that map every positive-rank minor M′ = (E′, I′) of M to an element e ∈ E′").

**Formalization Note.** Strategies are functions of the history (the moves so far), the standard
pure strategies of a finite perfect-information game, rather than functions of the current
minor. A minor `M / S ∖ C` forgets which removed elements were deleted and which contracted, and
the paper's own efficient strategies (Lemmas 5–7) are defined along the play. Both strategy
spaces give the same value (backward induction on a finite perfect-information game). The value
is an `Option` so that the strategy type is inhabited when the ground type is empty; legality
(`LegalMax`, `LegalMin`) demands `some e` at every position where the player has to move. -/
abbrev Strategy (α : Type*) : Type _ := List α → Option α

end MatroidOptGame


