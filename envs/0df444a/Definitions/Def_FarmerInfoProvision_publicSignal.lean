-- Prove2me | Definitions.Def_FarmerInfoProvision_publicSignal
-- name    : FarmerInfoProvision_publicSignal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:36:47.930157+00:00
-- url     : https://prove2.me/theorems/084a785f-edae-4e72-9ee7-a424212409c5
-- title:
--   Public signal $y=u+\epsilon_r$, $\epsilon_r\sim N(0,1/\beta)$
-- statement:
--   The central planner's noisy public signal is $y=u+\epsilon_r$ with $\epsilon_r\sim N(0,\sigma_r^2)$ independent of $u$ and of all private noises, and $\beta=1/\sigma_r^2$. In terms of the Gaussian primitive, $y=u+Z_{\mathrm{public}}/\sqrt\beta$.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), §3, p. 9

import Mathlib
import Definitions.Def_FarmerInfoProvision_demandShock

open MeasureTheory ProbabilityTheory

namespace FarmerInfoProvision

/-- **The noisy public signal `y = u + ϵ_r`, `ϵ_r ∼ N(0, 1/β)`.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), §3, p. 9: "We model the noisy public signal `y` as: `y = u + ϵ_r`,
where the noise `ϵ_r ∼ N(0, σ_r²)` is independent of `u` and all `{ϵ_i}`'s. We use
`β ≡ 1/σ_r²` to denote an exogenously given 'public information precision' parameter."

`publicSignal M α β = u + Z publicNoise / √β` with `u = demandShock M α`.

**Formalization Note.** Only `β > 0` is meaningful (a finite positive noise variance); the
theorems assume it. -/
noncomputable def publicSignal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (M : GaussianPrimitives P n) (α β : ℝ) : Ω → ℝ :=
  fun ω => demandShock M α ω + M.Z Shock.publicNoise ω / Real.sqrt β

end FarmerInfoProvision


