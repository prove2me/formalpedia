-- Prove2me | Definitions.Def_HighEntropyLimit_blackbody
-- name    : HighEntropyLimit_blackbody
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T21:52:34.678153+00:00
-- url     : https://prove2.me/theorems/459e6daf-4629-4d36-8e5f-538044acf0e6
-- title:
--   Planck and Rayleigh–Jeans spectra
-- statement:
--   With Planck's constant $h$, the speed of light $c$, frequency $\nu$ and inverse temperature $\beta = 1/(k_BT)$:
--
--   1. Planck's law (Eq. 6): $$B_{\mathrm{P}}(\nu,\beta) = \frac{2h\nu^3}{c^2}\,\frac{1}{e^{h\beta\nu}-1};$$
--   2. the Rayleigh–Jeans law (Eq. 5): $$B_{\mathrm{RJ}}(\nu,\beta) = \frac{2\nu^2}{c^2\beta}.$$
-- source:
--   Carcassi, Landini, Aidala, Classical mechanics as the high-entropy limit of quantum mechanics, arXiv:2411.00972v3 (1 Feb 2026), https://arxiv.org/abs/2411.00972, p. 5 Eqs. (5),(6)

import Mathlib

namespace HighEntropyLimit

/-- Planck's law, Eq. (6): `2hν³/c² · 1/(e^{hβν} - 1)`, with `β = 1/(k_B T)`. -/
noncomputable def planckSpectrum (h c ν β : ℝ) : ℝ :=
  2 * h * ν ^ 3 / c ^ 2 * (1 / (Real.exp (h * β * ν) - 1))

/-- The Rayleigh–Jeans law, Eq. (5): `2ν² k_B T / c² = 2ν² / (c² β)`. -/
noncomputable def rayleighJeansSpectrum (c ν β : ℝ) : ℝ :=
  2 * ν ^ 2 / (c ^ 2 * β)

end HighEntropyLimit


