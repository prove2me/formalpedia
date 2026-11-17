-- Prove2me | Definitions.Def_MatroidOptGame_Supplement_OracleAction
-- name    : MatroidOptGame_Supplement_OracleAction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:50:33.321635+00:00
-- url     : https://prove2.me/theorems/83165d2f-c540-463a-b91e-059cd433ed12
-- title:
--   One step of an oracle player: query or move
-- statement:
--   At its turn an oracle player performs a sequence of steps. Each step is either a **query** of a set $F\subseteq E$ to the independence oracle or a **move** $e\in E$, which ends the turn.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.2, pp.13, 15

import Mathlib

namespace MatroidOptGame.Supplement

/-- One step of an oracle player at its turn: ask the independence oracle about a set `F`, or make
the move `e`.
Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.2, pp.13 and 15 (players that "generate queries F̃₁, …, F̃ₛ to Õ" and then
move). -/
inductive OracleAction (α : Type*) where
  | query : Finset α → OracleAction α
  | move : α → OracleAction α

end MatroidOptGame.Supplement


