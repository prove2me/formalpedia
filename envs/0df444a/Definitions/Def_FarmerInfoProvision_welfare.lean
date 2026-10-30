-- Prove2me | Definitions.Def_FarmerInfoProvision_welfare
-- name    : FarmerInfoProvision_welfare
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:42:00.927919+00:00
-- url     : https://prove2.me/theorems/4adb59c3-c165-4ce6-9fe8-52d7f56b6a10
-- title:
--   Total expected farmer profit under a strategy profile
-- statement:
--   The farmers' total expected profit under the strategy profile $\sigma$ with informed set $I$ is $\sum_i\pi_i(\sigma)$. Evaluated at an equilibrium, it is the central planner's objective $n_1W^I+(n-n_1)W^J$ in (5).
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), §3, problem (5), p. 11

import Mathlib
import Definitions.Def_FarmerInfoProvision_expectedProfit

open MeasureTheory ProbabilityTheory

namespace FarmerInfoProvision

/-- **The farmers' total ex-ante expected profit under the strategy profile `σ`.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), §3, problem (5), p. 11: "to maximize farmers' total (ex-ante)
expected profit, the central planner solves: `S* = max W(n1, β; γ) ≡ max {n1 W^I(n1, β; γ) +
(n − n1) W^J(n1, β; γ)}`".

`welfare M a b c α β γ I σ = Σ_i expectedProfit M a b c α β γ I σ i`. Evaluated at an
equilibrium `σ` of the game with informed set `I` (`|I| = n1`), this is the paper's
`n1 W^I + (n − n1) W^J`. -/
noncomputable def welfare {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (M : GaussianPrimitives P n) (a b c α β γ : ℝ) (I : Finset (Fin n))
    (σ : Fin n → ℝ × ℝ → ℝ) : ℝ :=
  ∑ i, expectedProfit M a b c α β γ I σ i

end FarmerInfoProvision


