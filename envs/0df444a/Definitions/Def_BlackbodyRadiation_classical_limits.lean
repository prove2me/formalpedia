-- Prove2me | Definitions.Def_BlackbodyRadiation_classical_limits
-- name    : BlackbodyRadiation_classical_limits
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T13:22:43.052512+00:00
-- url     : https://prove2.me/theorems/d3b48b30-102a-4233-941e-3233e2caf551
-- title:
--   Rayleigh--Jeans and Wien spectral radiance $B^{\mathrm{RJ}}_\nu$, $B^{\mathrm{W}}_\nu$
-- statement:
--   Two classical predecessors of Planck's law, both written per unit **frequency** $\nu$ and
--   both left unit-agnostic by keeping the physical constants as real parameters: the Planck
--   constant $h$, the speed of light $c$, the Boltzmann constant $k_B$, and the absolute
--   temperature $T$.
--
--   The **Rayleigh-Jeans law** is what classical statistical mechanics predicts when every
--   mode of the radiation field receives the equipartition energy $k_BT$:
--
--   $$B^{\mathrm{RJ}}_\nu(\nu, T) \;=\; \frac{2\nu^2 k_B T}{c^2}.$$
--
--   It contains no reference to $h$ at all, matches the observed spectrum at long wavelengths,
--   and grows without bound as $\nu \to \infty$ - the ultraviolet catastrophe.
--
--   **Wien's distribution law** of 1896 is the opposite approximation, accurate at short
--   wavelengths and high temperatures:
--
--   $$B^{\mathrm{W}}_\nu(\nu, T) \;=\; \frac{2h\nu^3}{c^2}\exp\!\left(-\frac{h\nu}{k_B T}\right).$$
--
--   It is Planck's law with the Bose-Einstein denominator $e^{x}-1$ replaced by $e^{x}$, where
--   $x = h\nu/(k_BT)$.
--
--   Both are total real-valued functions of their arguments, defined for every real input with
--   no positivity restriction; statements built on them carry explicit positivity hypotheses.
--   They are given here as definitions only - nothing is asserted about them, and in
--   particular neither is related to Planck's law in this bundle.
-- source:
--   Planck constant, Wikipedia, https://en.wikipedia.org/wiki/Planck_constant , section "History", subsections "Origin of the constant" (Wien's law at short wavelengths, the Rayleigh-Jeans formula at long wavelengths, and Planck's spectral radiance per unit frequency) and "Development and application" (the ultraviolet catastrophe).

import Mathlib

namespace BlackbodyRadiation

/-- The Rayleigh–Jeans law, frequency parameterisation: the classical (equipartition)
spectral radiance of a black body at absolute temperature `T` per unit frequency `ν`,

  `B_ν^RJ(ν, T) = 2 ν² k_B T / c²`. -/
noncomputable def rayleighJeansFreq (c kB T ν : ℝ) : ℝ :=
  2 * ν ^ 2 * kB * T / c ^ 2

/-- Wien's 1896 distribution law, frequency parameterisation: the short-wavelength
(high-frequency) approximation to the black-body spectral radiance,

  `B_ν^W(ν, T) = (2 h ν³ / c²) * exp (- h ν / (k_B T))`. -/
noncomputable def wienFreq (h c kB T ν : ℝ) : ℝ :=
  2 * h * ν ^ 3 / c ^ 2 * Real.exp (-(h * ν / (kB * T)))

end BlackbodyRadiation


