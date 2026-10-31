-- Prove2me | Definitions.Def_DRBaseline_demandReduction
-- name    : DRBaseline_demandReduction
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:39:49.57672+00:00
-- url     : https://prove2.me/theorems/57a94f83-71f3-4d36-81ea-ecfc02d11d51
-- title:
--   Expected actual demand reduction $X(b,r)$
-- statement:
--   Let $s$ be a best-response selection, $\rho$ the probability of a demand-response event and $f(\omega)=\frac1{2\Omega}$ on $[0,2\Omega]$ the event-period demand density. The **expected actual demand reduction** is
--
--   $$X(b,r)=\rho\int_0^{2\Omega}s^*(b,r\mid\omega)\,f(\omega)\,d\omega .$$
--
--   **Formalization Note** An interval integral with the uniform density written out.
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, §4, p.13

import Mathlib

namespace DRBaseline

/-- **Expected actual demand reduction `X(b, r) = ρ ∫₀^{2Ω} s*(b, r | ω) f(ω) dω`.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, §4, p.13: "The expected value of the actual demand reduction is given by
X(b,r) = ρ ∫_0^{2Ω} s∗(·)f(ω)dω", with `f(ω) = 1/(2Ω)` on `[0, 2Ω]` (§3.1, p.7).

`s` is a best-response selection (`IsBestResponse`), with arguments `b, r, ω`.

**Formalization Note** The expectation is an interval integral with the uniform density
`1/(2Ω)` written out. -/
noncomputable def demandReduction (Ω ρ : ℝ) (s : ℝ → ℝ → ℝ → ℝ) (b r : ℝ) : ℝ :=
  ρ * ∫ ω in (0 : ℝ)..2 * Ω, s b r ω / (2 * Ω)

end DRBaseline


