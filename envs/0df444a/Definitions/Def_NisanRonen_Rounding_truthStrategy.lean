-- Prove2me | Definitions.Def_NisanRonen_Rounding_truthStrategy
-- name    : NisanRonen_Rounding_truthStrategy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:21:38.644228+00:00
-- url     : https://prove2.me/theorems/8359a02c-0733-4e60-9834-1ffa813fdfdf
-- title:
--   The truthful strategy
-- statement:
--   The **truthful strategy** of an agent of type $t^i$ declares its type, $d^i = t^i$, and executes every task $j$ allocated to it in minimal time, $e^i(x)_j = t^i_j$ for every allocation $x$.
--
--   A mechanism with verification is truthful if this strategy is dominant for every agent and type.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001) 166–196, doi:10.1006/game.1999.0790, Definition 19, p. 186 (PDF p. 21): "For each agent i of type t^i, there is a dominant strategy of the form a^i = (t^i, e^i())"; proof of Theorem 5.1, p. 188: "reveal its true type and … execute its tasks in minimal time"

import Mathlib
import Definitions.Def_NisanRonen_Rounding_Strategy

namespace NisanRonen.Rounding

/-- **The truthful strategy** of an agent of type `t^i` (Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001), Definition 19,
p. 186: "a dominant strategy of the form a^i = (t^i, e^i())"; proof of Theorem 5.1, p. 188: "to
reveal its true type and to execute its tasks in minimal time"): declare `t^i` and perform
every allocated task `j` in time `t^i_j`. -/
def truthStrategy {n k : ℕ} (ti : Fin k → ℝ) : Strategy n k :=
  ⟨ti, fun _ => ti⟩

end NisanRonen.Rounding


