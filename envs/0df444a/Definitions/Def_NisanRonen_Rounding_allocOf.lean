-- Prove2me | Definitions.Def_NisanRonen_Rounding_allocOf
-- name    : NisanRonen_Rounding_allocOf
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:18:01.604614+00:00
-- url     : https://prove2.me/theorems/49093746-9ac4-459c-9f6e-45eecc03080d
-- title:
--   Allocation produced by an algorithm on the rounded instance
-- statement:
--   An **allocation algorithm on rounded instances** is a map $f$ from rounded instances in $\delta$-units (lists of task columns of natural numbers) to lists of agents. Given declarations $d$, the allocation it produces assigns task $j$ to the $j$-th agent of the list $f(\mathrm{units}_\delta(d))$:
--
--   $$
--   x_f(d)(j) = f(\mathrm{units}_\delta(d))_j .
--   $$
--
--   In the rounding mechanism the allocation algorithm is "the rounding algorithm of Horowitz and Sahni (1976)", an exact solver of the rounded problem.
--
--   **Formalization Note** If the output list is too short, the missing entries default to agent $0$; the exact solvers considered output exactly one agent per task on every bounded instance, so the default is never used there.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001) 166–196, doi:10.1006/game.1999.0790, Definition 34, p. 193 (PDF p. 28): "The allocation algorithm is the rounding algorithm of Horowitz and Sahni (1976) sketched above"

import Mathlib
import Definitions.Def_NisanRonen_Rounding_units

namespace NisanRonen.Rounding

/-- **The allocation produced by an allocation algorithm on the rounded instance**
(Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001), Definition 34, p. 193: "The allocation algorithm is the rounding algorithm
of Horowitz and Sahni (1976) sketched above"). An algorithm `f` maps the δ-unit instance
(`units δ d`, one column per task) to a list of agents, the `j`-th entry being the agent that
receives task `j`; `allocOf f δ d j` reads that entry.

**Formalization Note** `getD j 0` returns agent `0` if the output list is too short; the
solvers considered (`IsExactRoundedSolver`) output exactly `k` entries on every in-box
instance, so this default is never used there. -/
noncomputable def allocOf {n k : ℕ} [NeZero n] (f : List (Fin n → ℕ) → List (Fin n)) (δ : ℝ)
    (d : Fin n → Fin k → ℝ) : Fin k → Fin n :=
  fun j => (f (units δ d)).getD j 0

end NisanRonen.Rounding


