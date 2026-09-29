-- Prove2me | Definitions.Def_CODATA2022_radiation_constants
-- name    : CODATA2022_radiation_constants
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T22:59:47.06498+00:00
-- url     : https://prove2.me/theorems/77b25104-7ff1-4bee-8573-5115115e4a8f
-- title:
--   Planck's law and the exactly known derived constants (CODATA 2022)
-- statement:
--   Planck's spectral radiance of a blackbody, in the frequency parameterization $B_\nu(T,\nu) = (2h\nu^3/c^2)/(e^{h\nu/kT}-1)$ and the wavelength parameterization $B_\lambda(T,\lambda) = (2hc^2/\lambda^5)/(e^{hc/(\lambda kT)}-1)$, together with the derived constants that the revised SI makes exactly known: the Stefan-Boltzmann constant $\sigma = (\pi^2/60)k^4/\hbar^3c^2$, the molar gas constant $R = N_Ak$, the Faraday constant $F = N_Ae$, the first and second radiation constants $c_1 = 2\pi hc^2$ and $c_2 = hc/k$, the Josephson constant $K_J = 2e/h$ and the von Klitzing constant $R_K = h/e^2$. All are numerical values in coherent SI units and are defined from the seven defining constants alone.
-- source:
--   Mohr, Newell, Taylor, Tiesinga, CODATA recommended values of the fundamental physical constants: 2022, Rev. Mod. Phys. 97, 025002 (2025), https://doi.org/10.1103/RevModPhys.97.025002, Tables XXXII and XXXIII (physicochemical constants; Stefan-Boltzmann constant, radiation constants, Wien displacement law constants) and the Nomenclature entry for $\sigma$.

import Mathlib
import Definitions.Def_CODATA2022_si_defining_constants

/-!
# Blackbody radiation and the exactly known derived constants (CODATA 2022)

Planck's spectral radiance (frequency and wavelength parameterizations) and the derived
constants that the 2019 revision of the SI made exactly known, as listed in
Mohr, Newell, Taylor, Tiesinga, Rev. Mod. Phys. **97**, 025002 (2025), Tables XXXII and
XXXIII and in the paper's Nomenclature.
-/

noncomputable section

namespace CODATA2022

/-- Planck's law in the frequency variable: the spectral radiance
`B_ν(T, ν) = 2hν³/c² · 1/(exp(hν/kT) − 1)` of a blackbody at thermodynamic temperature `T`,
in watts per square metre per steradian per hertz. -/
def spectralRadianceFrequency (T nu : ℝ) : ℝ :=
  2 * planckConstant * nu ^ 3 / speedOfLight ^ 2 /
    (Real.exp (planckConstant * nu / (boltzmannConstant * T)) - 1)

/-- Planck's law in the wavelength variable: the spectral radiance
`B_λ(T, λ) = 2hc²/λ⁵ · 1/(exp(hc/(λkT)) − 1)` of a blackbody at thermodynamic temperature `T`,
in watts per square metre per steradian per metre. -/
def spectralRadianceWavelength (T lam : ℝ) : ℝ :=
  2 * planckConstant * speedOfLight ^ 2 / lam ^ 5 /
    (Real.exp (planckConstant * speedOfLight / (lam * boltzmannConstant * T)) - 1)

/-- Stefan-Boltzmann constant `σ = (π²/60) k⁴ / (ℏ³c²)`, in watts per square metre per
kelvin to the fourth. -/
def stefanBoltzmannConstant : ℝ :=
  Real.pi ^ 2 / 60 * boltzmannConstant ^ 4 / (reducedPlanckConstant ^ 3 * speedOfLight ^ 2)

/-- Molar gas constant `R = N_A k`, in joules per mole per kelvin. -/
def molarGasConstant : ℝ := avogadroConstant * boltzmannConstant

/-- Faraday constant `F = N_A e`, in coulombs per mole. -/
def faradayConstant : ℝ := avogadroConstant * elementaryCharge

/-- First radiation constant `c₁ = 2πhc²`, in watt square metres. -/
def firstRadiationConstant : ℝ := 2 * Real.pi * planckConstant * speedOfLight ^ 2

/-- Second radiation constant `c₂ = hc/k`, in metre kelvins. -/
def secondRadiationConstant : ℝ := planckConstant * speedOfLight / boltzmannConstant

/-- Josephson constant `K_J = 2e/h`, in hertz per volt. -/
def josephsonConstant : ℝ := 2 * elementaryCharge / planckConstant

/-- von Klitzing constant `R_K = h/e²`, in ohms. -/
def vonKlitzingConstant : ℝ := planckConstant / elementaryCharge ^ 2

end CODATA2022

end


