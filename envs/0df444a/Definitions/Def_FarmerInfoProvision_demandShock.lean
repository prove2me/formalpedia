-- Prove2me | Definitions.Def_FarmerInfoProvision_demandShock
-- name    : FarmerInfoProvision_demandShock
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:35:59.484007+00:00
-- url     : https://prove2.me/theorems/c9cbdd59-5f4a-4ba0-a860-eaee20ca9c62
-- title:
--   Demand shock $u\sim N(0,1/\alpha)$
-- statement:
--   The price is $P(Q)=a-bQ+u$ with $u\sim N(0,\sigma_u^2)$ and $\alpha=1/\sigma_u^2$. In terms of the Gaussian primitive, $u=Z_{\mathrm{demand}}/\sqrt\alpha$, which has law $N(0,1/\alpha)$ for $\alpha>0$.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), §3, display (1), p. 8

import Mathlib
import Definitions.Def_FarmerInfoProvision_GaussianPrimitives

open MeasureTheory ProbabilityTheory

namespace FarmerInfoProvision

/-- **The demand shock `u ∼ N(0, 1/α)`.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), §3, display (1), p. 8: "`P(Q) = a − bQ + u`, … and
`u ∼ N(0, σ_u²)` represents future price uncertainty. We define `α ≡ 1/σ_u²`."

`demandShock M α = Z demand / √α`, which has law `N(0, 1/α)` when `α > 0`.

**Formalization Note.** Only `α > 0` is meaningful (a finite positive variance); the theorems
assume it. -/
noncomputable def demandShock {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (M : GaussianPrimitives P n) (α : ℝ) : Ω → ℝ :=
  fun ω => M.Z Shock.demand ω / Real.sqrt α

end FarmerInfoProvision


