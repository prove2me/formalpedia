-- Prove2me | Definitions.Def_MatroidOptGame_Supplement_OraclePlayer
-- name    : MatroidOptGame_Supplement_OraclePlayer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:51:03.017663+00:00
-- url     : https://prove2.me/theorems/bfcf874e-3d45-4f47-b4bb-45e2d45a7c68
-- title:
--   Deterministic adaptive oracle player
-- statement:
--   A **deterministic oracle player** is a rule that, at each step of its turn, sees
--
--   1. the history of the game (every move of both players so far), and
--   2. its own transcript: every query $F$ it has asked so far, in this turn and in earlier turns, with the oracle's answer ($1$ if $F$ is independent, $0$ otherwise),
--
--   and either asks another query or makes a move. It learns about the hidden matroid only through the oracle's answers. A **randomized** oracle player is a probability distribution on deterministic ones. These are the players of Theorems 11 and 14, which do not know the matroid the game is played on and can only query its independence oracle, before the first move and between moves.
--
--   **Formalization Note** Answers are integers, matching the published oracle `MatroidOptGame.indepOracle`; randomized players are `PMF`s on this type.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.2, Theorem 11 and its proof, pp.13–14; Theorem 14 and its proof, pp.15–16

import Mathlib
import Definitions.Def_MatroidOptGame_Supplement_OracleAction

namespace MatroidOptGame.Supplement

/-- A deterministic, adaptive oracle player: at each step of its turn it sees the game history
`h` (all moves so far, of both players) and its own transcript (every query it has asked so far,
in this and earlier turns, with the oracle's answer, `1` for independent and `0` for dependent),
and either asks a new query or moves. It sees nothing else of the hidden matroid.
Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.2, Theorem 11, p.13 ("MAX doesn't know which matroid M̃ the game is played on,
but can generate queries F̃₁, …, F̃ₛ to Õ"; the proof lets the queries depend on MIN's moves:
"we allow MAX to make the queries both before the first round and after the first round") and
Theorem 14, p.15–16 ("Answer queries of MIN as needed, including between moves").
**Formalization Note.** A randomized player is a probability distribution (`PMF`) on these
deterministic players ("We fix MAX's random choices", p.13; "Fix MIN's random choices", p.16).
Answers are integers, matching the published `MatroidOptGame.indepOracle`. -/
abbrev OraclePlayer (α : Type*) : Type _ :=
  List α → List (Finset α × ℤ) → OracleAction α

end MatroidOptGame.Supplement


