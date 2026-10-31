-- Prove2me | Definitions.Def_DRBaseline_underestimation
-- name    : DRBaseline_underestimation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:41:24.906672+00:00
-- url     : https://prove2.me/theorems/025564f8-276d-447f-890e-59d725636278
-- title:
--   Expected underestimation $X_u(b,r)$
-- statement:
--   When $b\le\omega\le\omega_1(b,r)$ the customer shifts enough demand to fall below the baseline, but the firm does not credit the amount $\omega-b$. The **expected underestimation** is
--
--   $$X_u(b,r)=\rho\int_{b}^{\omega_1(b,r)}(\omega-b)\,f(\omega)\,d\omega .$$
--
--   **Formalization Note** A set integral over $\{\omega: b\le\omega\le\omega_1(b,r)\}$, the region named on the page; it is $0$ when $b>\omega_1$ (in particular for $b>2\Omega$). An oriented integral would be negative there.
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, §4, p.13

import Mathlib
import Definitions.Def_DRBaseline_omega1

namespace DRBaseline

/-- **Expected underestimation `X_u(b, r) = ρ ∫_b^{ω₁(b,r)} (ω − b) f(ω) dω`.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, §4, p.13: "the expected value of underestimation is given by
X_u(b,r) = ρ ∫_b^{ω1(·)} (ω − b)f(ω)dω, where the firm underestimates a customer's demand
reduction by ω − b if b ≤ ω ≤ ω1(·)".

**Formalization Note** A set integral over `{ω : b ≤ ω ≤ ω₁(b, r)}`, the set named on the page.
It is empty, so `X_u = 0`, when `b > ω₁` (which happens for `b > 2Ω`, since `ω₁ ≤ 2Ω`); an
oriented integral `∫_b^{ω₁}` would instead be negative there. Since `ω₁ ≤ 2Ω`, the density
`1/(2Ω)` applies on the whole set. -/
noncomputable def underestimation (Ω cs ρ b r : ℝ) : ℝ :=
  ρ * ∫ ω in Set.Icc b (omega1 Ω cs b r), (ω - b) / (2 * Ω)

end DRBaseline


