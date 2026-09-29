-- Prove2me | Definitions.Def_OnlinePrimalDual_Framework_alg1X_lowerBound
-- name    : OnlinePrimalDual_Framework_alg1X_lowerBound
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:33:47.499951+00:00
-- url     : https://prove2.me/theorems/aa57af9c-8cb3-447d-bfb6-9ed2b3b563d6
-- title:
--   A lower-bound surrogate for Algorithm 1's primal value (book's Inequality (4.1))
-- statement:
--   The book's own Inequality (4.1) (p. 119): substituting the round-uniform bound `d` for the
--   per-round `|S(j)|` **inside the inequality's right-hand side only** (proved by induction on
--   the number of updates, using `|S(j)| ≤ d`), Algorithm 1's real `x_i` satisfies
--   `x_i ≥ (1/d)((1+1/c_i)^n − 1)` where `n = ∑_{j ∣ i ∈ S(j)} t_j` is the total increment count
--   touching `i`. `alg1X_lowerBound` names this right-hand side as its own quantity, a
--   lower-bound surrogate, never claimed to equal `alg1X` itself.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 119, inequality (4.1)

import Mathlib
import Definitions.Def_OnlinePrimalDual_Framework_CoveringInstance
import Definitions.Def_OnlinePrimalDual_Framework_dualSum

namespace OnlinePrimalDual.Framework

/-- A **lower-bound surrogate** for `alg1X`, *not* claimed to equal Algorithm 1's actual output.
This is the book's own Inequality (4.1) (p. 119): substituting the round-uniform bound `d` for
the per-round `|S(j)|` **inside the inequality's right-hand side only** (the book proves this by
induction on the number of updates, using `|S(j)| ≤ d`, p. 119), the algorithm's real `xᵢ`
satisfies `xᵢ ≥ (1/d)((1+1/cᵢ)^n − 1)` where `n` is the total increment count touching `i`. The
book never redefines the algorithm by this substitution — it is a one-directional bound used
inside the proof of Theorem 4.1, reproduced here as its own quantity so it is not confused with
`alg1X` itself. -/
noncomputable def alg1X_lowerBound {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (inst : CoveringInstance I J) (t : J → ℕ) (i : I) : ℝ :=
  (1 / inst.d) * ((1 + 1 / inst.c i) ^ (∑ j ∈ Finset.univ.filter (fun j => i ∈ inst.S j), t j) - 1)

end OnlinePrimalDual.Framework


