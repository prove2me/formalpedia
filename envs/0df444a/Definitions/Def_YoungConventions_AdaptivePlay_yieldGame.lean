-- Prove2me | Definitions.Def_YoungConventions_AdaptivePlay_yieldGame
-- name    : YoungConventions_AdaptivePlay_yieldGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:57:22.241632+00:00
-- url     : https://prove2.me/theorems/3ea3d8b2-caf7-4c8e-a07c-3d0f589983fd
-- title:
--   The Yield / Not Yield game of Example 2 (§4, p. 65)
-- statement:
--   The two-player game of Example 2, a version of "Battle of the Sexes". Row and Column each choose Yield or Not Yield. The payoffs (Row, Column) are:
--
--   | | Yield | Not Yield |
--   |---|---|---|
--   | **Yield** | $0, 0$ | $1, \sqrt 2$ |
--   | **Not Yield** | $\sqrt 2, 1$ | $0, 0$ |
--
--   Its strict pure Nash equilibria are (Yield, Not Yield) and (Not Yield, Yield). The game is used to show that without incomplete sampling adaptive play need not converge.
--
--   **Formalization Note** Players are `Fin 2` with $0$ = Row and $1$ = Column; strategies are `Bool` with `true` = Yield.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, Example 2, p. 65 (PDF p. 10)

import Mathlib

namespace YoungConventions.AdaptivePlay

/-- **The "Battle of the Sexes" of Example 2** (Young 1993, *The Evolution of Conventions*,
Econometrica 61:57–84, §4, Example 2, p. 65, PDF p. 10). Two players, Row and Column, each choose
Yield or Not Yield; the payoffs (Row, Column) are

|           | Yield     | Not Yield |
|-----------|-----------|-----------|
| Yield     | 0, 0      | 1, √2     |
| Not Yield | √2, 1     | 0, 0      |

**Formalization Note.** Players are `Fin 2`, with `0` = Row and `1` = Column. Each player's
strategies are `Bool`, with `true` = Yield and `false` = Not Yield. `yieldGame i s` is the payoff
of player `i` at the strategy pair `s`. -/
noncomputable def yieldGame : Fin 2 → (Fin 2 → Bool) → ℝ :=
  fun i s =>
    if i = 0 then
      (if s 0 = true ∧ s 1 = false then 1 else if s 0 = false ∧ s 1 = true then Real.sqrt 2 else 0)
    else
      (if s 0 = true ∧ s 1 = false then Real.sqrt 2 else if s 0 = false ∧ s 1 = true then 1 else 0)

end YoungConventions.AdaptivePlay


