-- Prove2me | Definitions.Def_OnlinePrimalDual_Framework_alg3X
-- name    : OnlinePrimalDual_Framework_alg3X
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:35:09.096984+00:00
-- url     : https://prove2.me/theorems/9ccffd77-b69d-4c52-9ae9-54b13be00c22
-- title:
--   Algorithm 3's (the complementary-slackness algorithm) final primal value
-- statement:
--   Algorithm 3's update rule (p. 124-125): step (1b) sets `x_i ← 1/d` exactly when
--   `∑_{j ∣ i ∈ S(j)} y_j` first reaches `c_i`; step (1c) then continuously updates `x_i` (while
--   `1/d ≤ x_i < 1`) via `x_i ← (1/d)exp(∑_{j ∣ i ∈ S(j)} y_j / c_i - 1)`. Evaluating this closed
--   form at the *final* accumulated dual sum, capped at `1` (matching the book's own proof, p. 125,
--   "the corresponding variable x_i cannot exceed 1"), reproduces the algorithm's final value
--   including its freeze once `x_i = 1`, since the closed form is monotone non-decreasing in the
--   accumulated sum. Before activation (accumulated sum below `c_i`), `x_i = 0`.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 124-125, Algorithm 3

import Mathlib
import Definitions.Def_OnlinePrimalDual_Framework_CoveringInstance
import Definitions.Def_OnlinePrimalDual_Framework_dualSum

namespace OnlinePrimalDual.Framework

/-- The final value Algorithm 3 (the complementary-slackness algorithm, p. 124, PDF p. 35)
assigns to primal variable `xᵢ`. Step (1b) sets `xᵢ ← 1/d` exactly when
`∑_{j | i ∈ S(j)} yⱼ` first reaches `cᵢ`; step (1c) then continuously updates `xᵢ` (while
`1/d ≤ xᵢ < 1`) by `xᵢ ← (1/d)exp((∑_{j | i ∈ S(j)} yⱼ)/cᵢ − 1)`. Since `dualSum inst y i` is
monotone non-decreasing in the process and this closed form is monotone in `dualSum`, evaluating
it at the *final* accumulated sum and capping at `1` (`min 1 …`, matching the book's own proof of
claim (2), p. 125, "the corresponding variable xᵢ cannot exceed 1") reproduces the same final
value as the step-by-step process, including its freeze once `xᵢ = 1`; before activation
(`dualSum inst y i < cᵢ`) the variable has not yet been touched by step (1b) and is `0`. -/
noncomputable def alg3X {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (inst : CoveringInstance I J) (y : J → ℝ) (i : I) : ℝ :=
  if dualSum inst y i < inst.c i then 0
  else min 1 ((1 / inst.d) * Real.exp (dualSum inst y i / inst.c i - 1))

end OnlinePrimalDual.Framework


