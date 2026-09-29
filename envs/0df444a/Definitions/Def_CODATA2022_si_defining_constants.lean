-- Prove2me | Definitions.Def_CODATA2022_si_defining_constants
-- name    : CODATA2022_si_defining_constants
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T22:59:06.140513+00:00
-- url     : https://prove2.me/theorems/c6f0c1a6-84db-4785-804d-72bd302022e1
-- title:
--   The seven defining constants of the SI (CODATA 2022)
-- statement:
--   The numerical values, in coherent SI units, of the seven constants whose values were fixed by the 2019 revision of the SI: the caesium-133 hyperfine transition frequency $\Delta\nu_{\mathrm{Cs}} = 9\,192\,631\,770\ \mathrm{Hz}$, the speed of light $c = 299\,792\,458\ \mathrm{m\,s^{-1}}$, the Planck constant $h = 6.626\,070\,15\times10^{-34}\ \mathrm{J\,s}$, the elementary charge $e = 1.602\,176\,634\times10^{-19}\ \mathrm{C}$, the Boltzmann constant $k = 1.380\,649\times10^{-23}\ \mathrm{J\,K^{-1}}$, the Avogadro constant $N_A = 6.022\,140\,76\times10^{23}\ \mathrm{mol^{-1}}$ and the luminous efficacy $K_{\mathrm{cd}} = 683\ \mathrm{lm\,W^{-1}}$, together with the reduced Planck constant $\hbar = h/2\pi$. Each is modelled as a real number: the numerical value of the quantity in the unit named in its docstring.
-- source:
--   Mohr, Newell, Taylor, Tiesinga, CODATA recommended values of the fundamental physical constants: 2022, Rev. Mod. Phys. 97, 025002 (2025), https://doi.org/10.1103/RevModPhys.97.025002, Table XXXII (defining constants, exact values).

import Mathlib

/-!
# The seven defining constants of the SI (CODATA 2022)

Numerical values are the exact ones fixed by the 2019 revision of the SI and listed in
Mohr, Newell, Taylor, Tiesinga, *CODATA recommended values of the fundamental physical
constants: 2022*, Rev. Mod. Phys. **97**, 025002 (2025), Table XXXII.
All quantities are pure real numbers: each is the numerical value of the constant in the
coherent SI unit named in its docstring.
-/

noncomputable section

namespace CODATA2022

/-- Numerical value of the unperturbed ground-state hyperfine transition frequency of the
caesium-133 atom `Δν_Cs`, in hertz. -/
def deltaNuCs : ℝ := 9192631770

/-- Numerical value of the speed of light in vacuum `c`, in metres per second. -/
def speedOfLight : ℝ := 299792458

/-- Numerical value of the Planck constant `h`, in joule seconds. -/
def planckConstant : ℝ := 6.62607015e-34

/-- Numerical value of the elementary charge `e`, in coulombs. -/
def elementaryCharge : ℝ := 1.602176634e-19

/-- Numerical value of the Boltzmann constant `k`, in joules per kelvin. -/
def boltzmannConstant : ℝ := 1.380649e-23

/-- Numerical value of the Avogadro constant `N_A`, in reciprocal moles. -/
def avogadroConstant : ℝ := 6.02214076e23

/-- Numerical value of the luminous efficacy of monochromatic radiation of frequency
`540 × 10^12 Hz`, `K_cd`, in lumens per watt. -/
def luminousEfficacy : ℝ := 683

/-- Reduced Planck constant `ℏ = h / 2π`, in joule seconds. -/
def reducedPlanckConstant : ℝ := planckConstant / (2 * Real.pi)

end CODATA2022

end


