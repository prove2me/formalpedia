-- Prove2me | Definitions.Def_TheoryOfGames_ThreePerson_ReducedThreePerson
-- name    : TheoryOfGames_ThreePerson_ReducedThreePerson
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T08:23:59.429991+00:00
-- url     : https://prove2.me/theorems/6e33b1f5-71eb-4944-a716-9e00d1968b41
-- title:
--   The reduced essential zero-sum three-person game (32:1) and the sets (32:6), (32:7)
-- statement:
--   The essential zero-sum three-person game in its reduced form with $\gamma = 1$ (32.1.1) has players $1, 2, 3$ and characteristic function
--   $$\text{(32:1)}\quad v(S) = \begin{cases} 0 & |S| = 0,\\ -1 & |S| = 1,\\ 1 & |S| = 2,\\ 0 & |S| = 3.\end{cases}$$
--   Its imputations are the vectors $\vec\alpha = \{\alpha_1, \alpha_2, \alpha_3\}$ with (32:2) $\alpha_1, \alpha_2, \alpha_3 \geqq -1$ and (32:3) $\alpha_1 + \alpha_2 + \alpha_3 = 0$ — the points of the fundamental triangle.
--
--   Two families of sets of imputations are named:
--
--   1. (32:6) the three-point set $\{-1, \tfrac12, \tfrac12\}, \{\tfrac12, -1, \tfrac12\}, \{\tfrac12, \tfrac12, -1\}$ (the middle points of the sides of the fundamental triangle);
--   2. (32:7), (32:7\*), (32:7\*\*) for a player $i$ and a number $c$: the set of all imputations with $\alpha_i = c$ (a line parallel to a side of the fundamental triangle, cut to the triangle).
--
--   These are the objects of the complete list of solutions (32:A), (32:B).
--
--   **Formalization Note** Players $1, 2, 3$ are `0, 1, 2 : Fin 3`. `redV S` is $-1$ if $|S| = 1$, $1$ if $|S| = 2$, and $0$ otherwise. `middlePointsSet` is the set of the three vectors `![-1, 1/2, 1/2]`, `![1/2, -1, 1/2]`, `![1/2, 1/2, -1]`; `lineSet i c` is the set of imputations of `redV` with `α i = c`, for every real `c` (the range (32:8) of `c` is imposed in the theorems, not here).
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 282, 32.1.1, (32:1); p. 283, (32:2), (32:3); p. 287, (32:6), (32:7); p. 288, (32:7*), (32:7**)

import Mathlib
import Definitions.Def_TheoryOfGames_ThreePerson_Solution

namespace TheoryOfGames.ThreePerson

/-- (32:1), 32.1.1: the characteristic function of the essential zero-sum three-person game in
its reduced form with `γ = 1`: `v(S) = 0, -1, 1, 0` when `S` has `0, 1, 2, 3` elements.
Players `1, 2, 3` of the book are `0, 1, 2 : Fin 3`. -/
def redV (S : Finset (Fin 3)) : ℝ :=
  if S.card = 1 then -1 else if S.card = 2 then 1 else 0

/-- (32:6), 32.2.1: the set of the three imputations
`{-1, ½, ½}, {½, -1, ½}, {½, ½, -1}` (the middle points of the sides of the fundamental
triangle). -/
noncomputable def middlePointsSet : Set (Fin 3 → ℝ) :=
  {![-1, 1 / 2, 1 / 2], ![1 / 2, -1, 1 / 2], ![1 / 2, 1 / 2, -1]}

/-- (32:7), (32:7*), (32:7**), 32.2.2: the set of all imputations `α` of `redV` with
`αᵢ = c` (`i = 0, 1, 2` is the book's player `1, 2, 3`). -/
def lineSet (i : Fin 3) (c : ℝ) : Set (Fin 3 → ℝ) :=
  {α | IsImputation redV α ∧ α i = c}

end TheoryOfGames.ThreePerson


