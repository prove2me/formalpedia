-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_Strat2
-- name    : YoungConventions_RiskDominance_Strat2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:57:20.46899+00:00
-- url     : https://prove2.me/theorems/6c485695-8f71-44cc-bb1b-4b8f471e808a
-- title:
--   Strategy sets of a $2\times2$ game
-- statement:
--   In a $2\times2$ matrix game there are two players, Row and Column, each with two strategies, which the paper calls $1$ and $2$.
--
--   **Formalization Note** Players are `0` (Row) and `1` (Column) in `Fin 2`, and the paper's strategies $1,2$ are `0, 1 : Fin 2`.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §7, p. 70

import Mathlib

namespace YoungConventions.RiskDominance

/-- **Strategy sets of a `2 × 2` game.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §7, p. 70 (PDF p. 15): "Let `Γ` be a `2 × 2` matrix
game". Each of the two players (Row = `0`, Column = `1`) has the two strategies `0` and `1`.

**Formalization Note.** The paper's strategies `1, 2` are `0, 1 : Fin 2`; its players Row and Column
are `0, 1 : Fin 2`. -/
abbrev Strat2 : Fin 2 → Type := fun _ => Fin 2

end YoungConventions.RiskDominance


