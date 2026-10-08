-- Prove2me | Definitions.Def_CooperationGraphs_FairRule_Game
-- name    : CooperationGraphs_FairRule_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:17:11.368263+00:00
-- url     : https://prove2.me/theorems/6602c900-d94f-4bcb-956c-25f9304f8774
-- title:
--   Finite transferable-utility games in characteristic-function form
-- statement:
--   Let $N$ be a nonempty finite set of players and $CL=\{S\subseteq N:S\ne\emptyset\}$ its nonempty coalitions. A game in characteristic-function form assigns a real worth to each coalition:
--   $$v\in\mathbb R^{CL},\qquad S\mapsto v_S. $$
--
--   The worth $v_S$ is the transferable wealth the players in $S$ can divide if they form. This general game carrier is shared by the graph-restricted game, superadditivity, and the allocation rule.
--
--   **Formalization Note.** Players are `Fin n`. The Lean type is `Finset (Fin n) → ℝ`; its value at $\emptyset$ is an unused coordinate, because the paper gives no empty-coalition worth. Every theorem assumes $0<n$, and every operation on games ignores that coordinate.
-- source:
--   Myerson, Graphs and Cooperation in Games, Discussion Paper No. 246 (Sept. 1976), §2, (1), p. 2

import Mathlib

namespace CooperationGraphs.FairRule

/-- A transferable-utility game on a finite player set. The source indexes values only by
nonempty coalitions. The coordinate at `∅` is ignored by every operation in this mission. -/
abbrev Game (n : ℕ) := Finset (Fin n) → ℝ

end CooperationGraphs.FairRule


