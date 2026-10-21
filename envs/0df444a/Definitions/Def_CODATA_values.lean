-- Prove2me | Definitions.Def_CODATA_values
-- name    : CODATA_values
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-21T01:30:13.784252+00:00
-- url     : https://prove2.me/theorems/7f8121b7-0341-4592-9800-cef0c5637a83
-- title:
--   The exact rational values of the CODATA 2022 constants
-- statement:
--   The exact rational values on which the 2022 adjustment rests, recorded
--   as exact rationals. The defining constants of the 2019 revision of
--   the SI: the speed of light c = 299 792 458 m s^-1, the Planck
--   constant h = 6.626 070 15 x 10^-34 J s, the elementary charge
--   e = 1.602 176 634 x 10^-19 C, the Boltzmann constant k = 1.380 649 x
--   10^-23 J K^-1, and the Avogadro constant N_A = 6.022 140 76 x 10^23
--   mol^-1. The derived exact quantities they determine: the Josephson
--   constant K_J = 2e/h, the von Klitzing constant R_K = h/e^2, the
--   magnetic flux quantum h/2e, the conductance quantum 2e^2/h and its
--   inverse, the Faraday constant N_A e, the molar gas constant N_A k,
--   the electronvolt e J, and the Planck constant in eV Hz^-1, h/e. The
--   2022 recommended rational values of the fine-structure-constant
--   family: alpha = 7.297 352 5643 x 10^-3, 1/alpha = 137.035 999 177,
--   mu_0 = 1.256 637 061 27 x 10^-6 N A^-2, eps_0 = 8.854 187 8188 x
--   10^-12 F m^-1, and Z_0 = 376.730 313 412 Ohm.
-- source:
--   P. J. Mohr, D. B. Newell, B. N. Taylor and E. Tiesinga, CODATA recommended values of the fundamental physical constants: 2022, J. Phys. Chem. Ref. Data 54, 033105 (2025), doi 10.1063/5.0279860; Rev. Mod. Phys. 97, 025002 (2025), doi 10.1103/RevModPhys.97.025002, Tables XXXII and XXXIII (the printed values and relative standard uncertainties of the recommended constants, with the derived exact quantities marked exact) and the exact defining values of the 2019 revision of the SI.

import Mathlib

/-!
# The CODATA 2022 adjustment: exact rational values of the constants

The third definition bundle of the mission: the exact rational values
of the constants of the 2019 revision of the International System of
Units that the 2022 CODATA adjustment takes as fixed (the speed of
light, the Planck constant, the elementary charge, the Boltzmann
constant and the Avogadro constant), the exact rational values of the
derived quantities they determine (the Josephson constant 2e/h, the
von Klitzing constant h/e^2, the magnetic flux quantum h/2e, the
conductance quantum 2e^2/h and its inverse, the Faraday constant
N_A e, the molar gas constant N_A k, and the electronvolt), and the
2022 recommended rational values of the fine-structure-constant family
(alpha, 1/alpha, mu_0, eps_0 and Z_0). The printed forms are those of
Table XXXII and Table XXXIII of the 2022 CODATA report (J. Phys. Chem.
Ref. Data 54, 033105 (2025); Rev. Mod. Phys. 97, 025002 (2025)).
-/

namespace CODATA

/-- The speed of light in vacuum, c, exactly 299 792 458 m s⁻¹. -/
def cVal : ℚ := 299792458

/-- The Planck constant, h, exactly 6.626 070 15 × 10⁻³⁴ J s. -/
def hVal : ℚ := 662607015 / (10:ℚ)^42

/-- The elementary charge, e, exactly 1.602 176 634 × 10⁻¹⁹ C. -/
def eVal : ℚ := 1602176634 / (10:ℚ)^28

/-- The Boltzmann constant, k, exactly 1.380 649 × 10⁻²³ J K⁻¹. -/
def kVal : ℚ := 1380649 / (10:ℚ)^29

/-- The Avogadro constant, N_A, exactly 6.022 140 76 × 10²³ mol⁻¹. -/
def naVal : ℚ := 602214076 * (10:ℚ)^15

/-- The Josephson constant, K_J = 2e/h, exactly
483 597.848 4 ... GHz V⁻¹ (Table XXXIII). -/
def kjVal : ℚ := 2 * eVal / hVal

/-- The von Klitzing constant, R_K = h/e², exactly
25 812.807 45 ... Ω (Table XXXIII). -/
def rkVal : ℚ := hVal / (eVal * eVal)

/-- The magnetic flux quantum, Phi_0 = h/2e, exactly
2.067 833 848 ... × 10⁻¹⁵ Wb (Table XXXIII). -/
def phi0Val : ℚ := hVal / (2 * eVal)

/-- The conductance quantum, G_0 = 2e²/h, exactly
7.748 091 729 ... × 10⁻⁵ S (Table XXXIII). -/
def g0Val : ℚ := 2 * eVal * eVal / hVal

/-- The inverse conductance quantum, G_0⁻¹ = h/2e², exactly
12 906.403 72 ... Ω (Table XXXIII). -/
def g0invVal : ℚ := hVal / (2 * eVal * eVal)

/-- The Faraday constant, F = N_A e, exactly
96 485.332 12 ... C mol⁻¹ (Table XXXIII). -/
def faradayVal : ℚ := naVal * eVal

/-- The molar gas constant, R = N_A k, exactly
8.314 462 618 ... J mol⁻¹ K⁻¹ (Table XXXIII). -/
def gasVal : ℚ := naVal * kVal

/-- The electronvolt-joule conversion factor, 1 eV = e J, exactly
1.602 176 634 × 10⁻¹⁹ J (Table XXXIII). -/
def eVoltVal : ℚ := eVal

/-- The Planck constant in the units eV Hz⁻¹, h/e, exactly
4.135 667 696 ... × 10⁻¹⁵ eV Hz⁻¹ (Table XXXIII). -/
def h_eV : ℚ := hVal / eVal

/-- The fine-structure constant, alpha: 2022 recommended value
7.297 352 5643(11) × 10⁻³ (Table XXXIII). -/
def alphaVal : ℚ := 72973525643 / (10:ℚ)^13

/-- The inverse fine-structure constant: 2022 recommended value
137.035 999 177(21) (Table XXXIII). -/
def alphaInvVal : ℚ := 137035999177 / (10:ℚ)^9

/-- The vacuum magnetic permeability, mu_0: 2022 recommended value
1.256 637 061 27(20) × 10⁻⁶ N A⁻² (Table XXXIII). -/
def mu0Val : ℚ := 125663706127 / (10:ℚ)^17

/-- The vacuum electric permittivity, eps_0: 2022 recommended value
8.854 187 8188(14) × 10⁻¹² F m⁻¹ (Table XXXIII). -/
def eps0Val : ℚ := 88541878188 / (10:ℚ)^22

/-- The impedance of vacuum, Z_0: 2022 recommended value
376.730 313 412(58) Ω (Table XXXIII). -/
def z0Val : ℚ := 376730313412 / (10:ℚ)^9

end CODATA


