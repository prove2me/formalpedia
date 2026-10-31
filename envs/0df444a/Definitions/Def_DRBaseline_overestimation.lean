-- Prove2me | Definitions.Def_DRBaseline_overestimation
-- name    : DRBaseline_overestimation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:39:51.883748+00:00
-- url     : https://prove2.me/theorems/de653a20-3715-4bc8-8931-f27c34df34c1
-- title:
--   Expected overestimation $X_o(b)$
-- statement:
--   When demand $\omega$ is below the baseline $b$, the firm overestimates the customer's reduction by $b-\omega$. The **expected overestimation** is
--
--   $$X_o(b)=\rho\int_0^{b}(b-\omega)\,f(\omega)\,d\omega,$$
--
--   with $f(\omega)=\frac1{2\Omega}$ on $[0,2\Omega]$ and $0$ elsewhere. For $b\le2\Omega$ it equals $\rho b^2/(4\Omega)$.
--
--   **Formalization Note** Since the density vanishes above $2\Omega$, the integral is taken over $(0,\min(b,2\Omega)]$; for $b\le2\Omega$ this is the printed integral. It is $0$ for $b\le0$.
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, §4, p.13

import Mathlib

namespace DRBaseline

/-- **Expected overestimation `X_o(b) = ρ ∫₀^b (b − ω) f(ω) dω`.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, §4, p.13: "The expected value of overestimation is given by X_o(b) = ρ ∫_0^b (b − ω)f(ω)dω,
where the firm overestimates a customer's demand reduction by b − ω if ω < b".

**Formalization Note** The density `f(ω) = 1/(2Ω)` vanishes above `2Ω` (§3.1, p.7), so the
integral runs over `(0, min(b, 2Ω)]`; for `b ≤ 2Ω` this is the printed `∫_0^b`, and it equals
`ρb²/(4Ω)` there. A set integral over `Set.Ioc`, so it is `0` for `b ≤ 0`. -/
noncomputable def overestimation (Ω ρ b : ℝ) : ℝ :=
  ρ * ∫ ω in Set.Ioc 0 (min b (2 * Ω)), (b - ω) / (2 * Ω)

end DRBaseline


