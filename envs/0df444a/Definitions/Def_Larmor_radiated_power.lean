-- Prove2me | Definitions.Def_Larmor_radiated_power
-- name    : Larmor_radiated_power
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T01:06:19.880661+00:00
-- url     : https://prove2.me/theorems/f4eb98e0-7e41-478b-99e6-d92f378f405a
-- title:
--   Radiated power as the flux of the Poynting vector through a sphere
-- statement:
--   This file defines the quantity that the Larmor formula evaluates.
--
--   Given an electric field $E$ and a magnetic field $B$ on space, both taken at one instant, and a radius $R$, the **power crossing the sphere of radius $R$ centred at the origin** is the flux of the Poynting vector $S=\varepsilon_0c^2(E\times B)$ through that sphere, measured with the outward unit normal $n(x)=x/R$:
--
--   $$P(R)=\int_{\|x\|=R}\bigl\langle S(x),\;x/R\bigr\rangle\;\mathrm d\mathcal H^2(x).$$
--
--   The integral is taken against the two-dimensional Hausdorff measure $\mathcal H^2$ restricted to the sphere, which on a two-dimensional surface in $\mathbb{R}^3$ is the ordinary surface-area measure; for the sphere of radius $R$ it has total mass $4\pi R^2$.
--
--   Poynting's theorem identifies this surface integral with the rate at which electromagnetic energy leaves the ball of radius $R$, which is why it is called the radiated power.
--
--   **Formalization Note** The measure used is `μH[2]` restricted to `Metric.sphere 0 R`, and the normal is written as $R^{-1}x$, which is the outward unit normal for $R>0$. The definition does not presuppose integrability: when the integrand is not integrable the Bochner integral returns $0$.
-- source:
--   https://en.wikipedia.org/wiki/Larmor_formula — Derivation section: "To calculate the power radiated by a point charge ... we integrate the Poynting vector over the surface of a sphere of radius R"; J. D. Jackson, Classical Electrodynamics, 3rd ed., Wiley 1998, §14.2.

import Definitions.Def_Larmor_em_fields

open MeasureTheory

namespace Larmor

/-- The power crossing the sphere of radius `R` centred at the origin: the flux of the
Poynting vector through that sphere, integrated against the two-dimensional Hausdorff
(surface) measure, with the outward unit normal `x / R`. -/
noncomputable def radiatedFlux (ε₀ c : ℝ) (E B : Vec → Vec) (R : ℝ) : ℝ :=
  ∫ x in Metric.sphere (0 : Vec) R, inner ℝ (poynting ε₀ c (E x) (B x)) (R⁻¹ • x) ∂(μH[2])

end Larmor


