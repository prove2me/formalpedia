-- Prove2me | Definitions.Def_elementary_charge_si_constants
-- name    : elementary_charge_si_constants
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T16:07:11.009786+00:00
-- url     : https://prove2.me/theorems/ffe4ed92-08f3-4b31-95e3-cd167cccf19a
-- title:
--   The 2019 SI defining constants and the derived electrical constants
-- statement:
--   The definition layer of the mission. It fixes, as exact rational real numbers, the four 2019 SI defining constants used in the source: the elementary charge $e = 1.602176634\times10^{-19}$ C, the Avogadro constant $N_\mathrm{A} = 6.02214076\times10^{23}\ \mathrm{mol}^{-1}$, the Planck constant $h = 6.62607015\times10^{-34}$ J s and the speed of light $c = 299792458$ m/s. It then defines, as functions of their arguments rather than as fixed numbers, the Faraday constant $F = N_\mathrm{A}e$, the Josephson constant $K_\mathrm{J} = 2e/h$, the von Klitzing constant $R_\mathrm{K} = h/e^2$, the fine-structure constant in CODATA form $\alpha = \mu_0 c e^2/(2h)$, and the natural unit of charge $q_0 = \sqrt{4\pi\varepsilon_0\hbar c}$. Units are implicit: each constant is a bare real number in the SI unit named in its docstring.
-- source:
--   "Elementary charge", Wikipedia, https://en.wikipedia.org/wiki/Elementary_charge (uploaded PDF revision). Sections: "As a unit"; "Quantization"; "Lack of fractional charges"; "In terms of the Avogadro constant and Faraday constant"; "From the Josephson and von Klitzing constants"; "CODATA method".

import Mathlib

namespace ElementaryCharge

/-- The elementary charge `e`, in coulombs.  Fixed exactly by the 2019 revision
of the SI: `e = 1.602176634 × 10⁻¹⁹ C`. -/
noncomputable def eSI : ℝ := 1602176634 / 10 ^ 28

/-- The Avogadro constant `N_A`, in `mol⁻¹`.  Fixed exactly by the 2019
revision of the SI: `N_A = 6.02214076 × 10²³ mol⁻¹`. -/
noncomputable def avogadroSI : ℝ := 602214076 * 10 ^ 15

/-- The Planck constant `h`, in `J s`.  Fixed exactly by the 2019 revision of
the SI: `h = 6.62607015 × 10⁻³⁴ J s`. -/
noncomputable def planckSI : ℝ := 662607015 / 10 ^ 42

/-- The speed of light in vacuum `c`, in `m s⁻¹`: `c = 299792458 m/s` exactly. -/
noncomputable def lightSpeedSI : ℝ := 299792458

/-- The Faraday constant `F = N_A e`: the charge of one mole of electrons. -/
noncomputable def faradayConstant (NA q : ℝ) : ℝ := NA * q

/-- The Josephson constant `K_J = 2e/h`. -/
noncomputable def josephsonConstant (q hPlanck : ℝ) : ℝ := 2 * q / hPlanck

/-- The von Klitzing constant `R_K = h/e²`. -/
noncomputable def vonKlitzingConstant (q hPlanck : ℝ) : ℝ := hPlanck / q ^ 2

/-- The fine-structure constant in the form used by the CODATA relation,
`α = μ₀ c e² / (2h)`. -/
noncomputable def fineStructureConstant (q hPlanck mu0 cLight : ℝ) : ℝ :=
  mu0 * cLight * q ^ 2 / (2 * hPlanck)

/-- The natural unit of charge `q₀ = √(4π ε₀ ħ c)`, for which the fine-structure
constant equals `(e/q₀)²`. -/
noncomputable def naturalUnitCharge (eps0 hbar cLight : ℝ) : ℝ :=
  Real.sqrt (4 * Real.pi * eps0 * hbar * cLight)

end ElementaryCharge


