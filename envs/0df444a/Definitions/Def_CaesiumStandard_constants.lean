-- Prove2me | Definitions.Def_CaesiumStandard_constants
-- name    : CaesiumStandard_constants
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T15:44:20.139912+00:00
-- url     : https://prove2.me/theorems/1d882d92-0763-4816-ad52-b500541c9a7a
-- title:
--   SI defining constants and caesium-133 radiation parameters
-- statement:
--   The seven SI defining constants, and the parameters of the caesium-133
--   hyperfine transition radiation derived from them, as exact rational numbers.
--
--   Since the 2019 revision of the SI, each defining constant has an exact decimal value:
--
--   $$\Delta\nu_{\mathrm{Cs}} = 9\,192\,631\,770\ \mathrm{Hz},\quad c = 299\,792\,458\ \mathrm{m/s},\quad h = 6.626\,070\,15\times 10^{-34}\ \mathrm{J\,s},$$
--
--   $$e = 1.602\,176\,634\times 10^{-19}\ \mathrm C,\quad k = 1.380\,649\times 10^{-23}\ \mathrm{J/K},$$
--
--   $$N_{\mathrm A} = 6.022\,140\,76\times 10^{23}\ \mathrm{mol^{-1}},\quad K_{\mathrm{cd}} = 683\ \mathrm{lm/W}.$$
--
--   Each is recorded here as the *numerical value* of the constant in the stated unit, an
--   element of $\mathbb Q$; no dimension is attached and no floating-point rounding occurs.
--
--   From them the four parameters of the caesium radiation are formed,
--
--   $$\Delta t_{\mathrm{Cs}} = \frac{1}{\Delta\nu_{\mathrm{Cs}}},\qquad \Delta\lambda_{\mathrm{Cs}} = \frac{c}{\Delta\nu_{\mathrm{Cs}}},\qquad \Delta E_{\mathrm{Cs}} = h\,\Delta\nu_{\mathrm{Cs}},\qquad \Delta M_{\mathrm{Cs}} = \frac{\Delta E_{\mathrm{Cs}}}{c^{2}},$$
--
--   together with the corresponding parameters of the $540\ \mathrm{THz}$ radiation used in the
--   definition of the candela, and the luminous energy $K_{\mathrm{cd}}\,h\,\nu_{\mathrm{opt}}$ carried
--   by one of its photons.
--
--   Finally the file records the *Summary* section's formula for each of the seven base units, and
--   the *Electromagnetic units* formula for the coulomb, as functions of a caesium frequency $\nu$
--   left variable while all other defining constants stay fixed. These are written
--   $s(\nu), m(\nu), \mathrm{kg}(\nu), \mathrm A(\nu), \mathrm K(\nu), \mathrm{mol}(\nu),
--   \mathrm{cd}(\nu), \mathrm C(\nu)$; the formulas for the mole and the coulomb do not contain
--   $\nu$ at all.
--
--   This is the shared model for every statement of the mission: any development about SI
--   conversion factors can import it instead of re-transcribing the decimals.
-- source:
--   "Caesium standard", Wikipedia, revision 1328818072, https://en.wikipedia.org/w/index.php?title=Caesium_standard&oldid=1328818072 — sections 'Technical details', 'Parameters and significance in the second and other SI units', 'Summary'

import Mathlib

/-!
# The caesium standard: SI defining constants and caesium-133 radiation parameters

Every quantity below is an **exact rational number**: the numerical value of a physical
quantity when expressed in the corresponding SI unit (hertz for a frequency, metres per
second for a speed, and so on). The 2019 SI fixes each of the seven defining constants to
an exact decimal value, so no approximation is involved.

Source: "Caesium standard", Wikipedia, sections *Technical details*, *Parameters and
significance in the second and other SI units*, and *Summary*.
-/

namespace CaesiumStandard

/-- `ΔνCs`, the unperturbed ground-state hyperfine transition frequency of the caesium-133
atom, in hertz: exactly `9 192 631 770`. -/
def dnuCs : ℚ := 9192631770

/-- `c`, the speed of light in vacuum, in metres per second: exactly `299 792 458`. -/
def cLight : ℚ := 299792458

/-- `h`, the Planck constant, in joule seconds: exactly `6.626 070 15 × 10⁻³⁴`. -/
def hPlanck : ℚ := 6.62607015e-34

/-- `e`, the elementary charge, in coulombs: exactly `1.602 176 634 × 10⁻¹⁹`. -/
def eCharge : ℚ := 1.602176634e-19

/-- `k`, the Boltzmann constant, in joules per kelvin: exactly `1.380 649 × 10⁻²³`. -/
def kBoltzmann : ℚ := 1.380649e-23

/-- `N_A`, the Avogadro constant, in reciprocal moles: exactly `6.022 140 76 × 10²³`. -/
def nAvogadro : ℚ := 6.02214076e23

/-- `K_cd`, the luminous efficacy of monochromatic radiation of frequency `540 THz`,
in lumens per watt: exactly `683`. -/
def kcdLumEff : ℚ := 683

/-- `ΔtCs = 1 / ΔνCs`, the period of the caesium-133 hyperfine transition radiation,
in seconds. -/
def tCs : ℚ := 1 / dnuCs

/-- `ΔλCs = c / ΔνCs`, the wavelength of the caesium-133 hyperfine transition radiation,
in metres. -/
def lambdaCs : ℚ := cLight / dnuCs

/-- `ΔECs = h ΔνCs`, the energy of one photon of the caesium-133 hyperfine transition
radiation, in joules. -/
def ECs : ℚ := hPlanck * dnuCs

/-- `ΔMCs = ΔECs / c²`, the mass equivalent of one photon of the caesium-133 hyperfine
transition radiation, in kilograms. -/
def MCs : ℚ := ECs / cLight ^ 2

/-!
## The 540 THz reference radiation used for the optical units
-/

/-- The frequency, in hertz, of the monochromatic radiation used in the definition of the
candela: exactly `5.4 × 10¹⁴`. -/
def nuOpt : ℚ := 5.4e14

/-- The period `1 / (540 THz)`, in seconds. -/
def tOpt : ℚ := 1 / nuOpt

/-- The wavelength `c / (540 THz)`, in metres. -/
def lambdaOpt : ℚ := cLight / nuOpt

/-- The photon energy `h · (540 THz)`, in joules. -/
def EOpt : ℚ := hPlanck * nuOpt

/-- The luminous energy carried by one photon of the 540 THz radiation, `K_cd · h ·
(540 THz)`, in lumen seconds. -/
def luminousEnergyPerPhotonOpt : ℚ := EOpt * kcdLumEff

/-!
## The base units as functions of the caesium frequency

The seven expressions below are the *Summary* section's formulas for the SI base units in
terms of the defining constants, with the caesium frequency left as a parameter `nu`
(in hertz) instead of being fixed to `ΔνCs`. All other defining constants keep their fixed
values. Each function returns the numerical value that the formula produces; at
`nu = dnuCs` every one of them is expected to return `1`.
-/

/-- The *Summary* formula for one second, `9 192 631 770 / ΔνCs`, at caesium frequency
`nu`. -/
def secondIn (nu : ℚ) : ℚ := 9192631770 / nu

/-- The *Summary* formula for one metre, `(9 192 631 770 / 299 792 458) · c / ΔνCs`, at
caesium frequency `nu`. -/
def metreIn (nu : ℚ) : ℚ := (9192631770 / 299792458) * (cLight / nu)

/-- The *Summary* formula for one kilogram,
`(8.987 551 787 368 1764 × 10⁴⁰ / 6.091 102 297 113 866 55) · h ΔνCs / c²`, at caesium
frequency `nu`. -/
def kilogramIn (nu : ℚ) : ℚ :=
  (8.9875517873681764e40 / 6.09110229711386655) * (hPlanck * nu / cLight ^ 2)

/-- The *Summary* formula for one ampere, `(10⁹ / 1.472 821 982 686 006 218) · e ΔνCs`, at
caesium frequency `nu`. -/
def ampereIn (nu : ℚ) : ℚ := (1e9 / 1.472821982686006218) * (eCharge * nu)

/-- The *Summary* formula for one kelvin,
`(13.806 49 / 6.091 102 297 113 866 55) · h ΔνCs / k`, at caesium frequency `nu`. -/
def kelvinIn (nu : ℚ) : ℚ :=
  (13.80649 / 6.09110229711386655) * (hPlanck * nu / kBoltzmann)

/-- The *Summary* formula for one mole, `6.022 140 76 × 10²³ / N_A`, at caesium frequency
`nu`. The caesium frequency does not occur in this formula, so the parameter is unused. -/
def moleIn (_nu : ℚ) : ℚ := 6.02214076e23 / nAvogadro

/-- The *Summary* formula for one candela,
`(10¹¹ / 3.824 339 691 519 516 481 631 301 046 05) · h ΔνCs² K_cd`, at caesium frequency
`nu`. -/
def candelaIn (nu : ℚ) : ℚ :=
  (1e11 / 3.82433969151951648163130104605) * (hPlanck * nu ^ 2 * kcdLumEff)

/-- The *Electromagnetic units* formula for one coulomb, `(10¹⁹ / 1.602 176 634) · e`, at
caesium frequency `nu`. The caesium frequency does not occur in this formula, so the
parameter is unused. -/
def coulombIn (_nu : ℚ) : ℚ := (1e19 / 1.602176634) * eCharge

end CaesiumStandard


