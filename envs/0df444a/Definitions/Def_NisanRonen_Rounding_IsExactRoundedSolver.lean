-- Prove2me | Definitions.Def_NisanRonen_Rounding_IsExactRoundedSolver
-- name    : NisanRonen_Rounding_IsExactRoundedSolver
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:22:15.423074+00:00
-- url     : https://prove2.me/theorems/e51d3a07-8084-453d-95d7-a9c76b45441e
-- title:
--   Exact solver of the rounded bounded scheduling problem
-- statement:
--   Let $\delta > 0$ and $0 < a < b$. An allocation algorithm $f$ on rounded instances is an **exact solver of the rounded problem** if, for every number $k$ of tasks and every matrix of declared times $d \in [a,b]^{n \times k}$,
--
--   1. $f$ outputs exactly one agent per task, and
--   2. the allocation $x = x_f(d)$ minimizes the rounded make-span on $d$:
--
--   $$
--   \hat g\big(x, \mathrm{corr}^*(x, d)\big) \le \hat g\big(y, \mathrm{corr}^*(y, d)\big) \quad \text{for every allocation } y .
--   $$
--
--   This is the property of the rounding algorithm of Horowitz and Sahni used by the rounding mechanism. Ties among optimal allocations may be broken in any way, and nothing is required outside the box $[a,b]$.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001) 166–196, doi:10.1006/game.1999.0790, p. 192 (PDF p. 27): "It then exactly solves this rounded problem using dynamic programming (in polynomial time)"; Definition 34, p. 193

import Mathlib
import Definitions.Def_NisanRonen_Rounding_roundedMakespan
import Definitions.Def_NisanRonen_Rounding_corrStar
import Definitions.Def_NisanRonen_Rounding_allocOf

namespace NisanRonen.Rounding

/-- **Exact solver of the rounded bounded scheduling problem** (Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001), p. 192: "The
entries t^i_j are first rounded up to integer multiples of δ … It then exactly solves this
rounded problem using dynamic programming"). An algorithm `f` on δ-unit instances is an exact
rounded solver for the box `[a, b]` if, on every declaration matrix `d` with all entries in
`[a, b]` (any number `k` of tasks), it outputs one agent per task and the allocation
`x = allocOf f δ d` minimizes the rounded make-span:
`ĝ(x, corr*(x, d)) ≤ ĝ(y, corr*(y, d))` for every allocation `y`.

**Formalization Note** Nothing is required of `f` outside the box; ties among optimal
allocations may be broken in any way. -/
def IsExactRoundedSolver {n : ℕ} [NeZero n] (f : List (Fin n → ℕ) → List (Fin n))
    (δ a b : ℝ) : Prop :=
  ∀ (k : ℕ) (d : Fin n → Fin k → ℝ), (∀ i j, a ≤ d i j ∧ d i j ≤ b) →
    (f (units δ d)).length = k ∧
      ∀ y : Fin k → Fin n,
        roundedMakespan δ (allocOf f δ d) (corrStar (allocOf f δ d) d) ≤
          roundedMakespan δ y (corrStar y d)

end NisanRonen.Rounding


