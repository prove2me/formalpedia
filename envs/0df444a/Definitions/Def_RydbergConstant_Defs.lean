-- Prove2me | Definitions.Def_RydbergConstant_Defs
-- name    : RydbergConstant_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T20:13:26.413919+00:00
-- url     : https://prove2.me/theorems/8c17767b-45c1-4919-84ba-d7dee03f457b
-- title:
--   Rydberg constant: physical constants, derived atomic scales, Bohr orbits
-- statement:
--   Definitions shared by every statement of the mission.
--
--   1. A bundle $K$ of five strictly positive reals: electron rest mass $m_e$, elementary charge $e$, vacuum permittivity $\varepsilon_0$, Planck constant $h$, speed of light $c$.
--   2. The Rydberg constant for infinite nuclear mass $R_\infty=\dfrac{m_ee^4}{8\varepsilon_0^2h^3c}$.
--   3. $\hbar=h/(2\pi)$; the fine-structure constant $\alpha=\dfrac{1}{4\pi\varepsilon_0}\dfrac{e^2}{\hbar c}$.
--   4. Compton wavelength $\lambda_e=h/(m_ec)$, Compton frequency $f_C=m_ec^2/h$, Compton angular frequency $\omega_C=2\pi f_C$.
--   5. Bohr radius $a_0=4\pi\varepsilon_0\hbar^2/(e^2m_e)$ and classical electron radius $r_e=\dfrac{1}{4\pi\varepsilon_0}\dfrac{e^2}{m_ec^2}$.
--   6. Rydberg unit of energy $\mathrm{Ry}=hcR_\infty$.
--   7. Reduced mass $\mu(M)=1/(1/m_e+1/M)$ and corrected Rydberg constant $R_M=(\mu(M)/m_e)R_\infty$.
--   8. A Bohr orbit of a particle of mass $m$ with quantum number $n$: radius $r>0$, speed $v>0$ with $\dfrac{mv^2}{r}=\dfrac{e^2}{4\pi\varepsilon_0r^2}$ and $mvr=n\hbar$.
--   9. The orbit energy $E=\tfrac12mv^2-\dfrac{e^2}{4\pi\varepsilon_0r}$.
--
--   These are exactly the formulas of the source's Value, Bohr model and Alternative expressions sections.
--
--   **Formalization Note** $\mu(M)$ and $R_M$ are defined for every real $M$ (Lean's division returns $0$ on division by zero); all theorems using them assume $M>0$.
-- source:
--   Wikipedia, "Rydberg constant", revision oldid=1341645811 (https://en.wikipedia.org/w/index.php?title=Rydberg_constant&oldid=1341645811), sections Value, Bohr model, Alternative expressions

import Mathlib

namespace RydbergConstant

/-- The fundamental constants entering the Rydberg constant, all positive reals
(SI values are not fixed): electron rest mass `me`, elementary charge `e`,
vacuum permittivity `ε0`, Planck constant `h`, speed of light `c`. -/
structure Constants where
  me : ℝ
  e : ℝ
  ε0 : ℝ
  h : ℝ
  c : ℝ
  me_pos : 0 < me
  e_pos : 0 < e
  ε0_pos : 0 < ε0
  h_pos : 0 < h
  c_pos : 0 < c

variable (K : Constants)

/-- Rydberg constant for infinite nuclear mass: `R∞ = mₑ e⁴ / (8 ε₀² h³ c)`. -/
noncomputable def rydbergInf : ℝ :=
  K.me * K.e ^ 4 / (8 * K.ε0 ^ 2 * K.h ^ 3 * K.c)

/-- Reduced Planck constant `ħ = h / (2π)`. -/
noncomputable def hbar : ℝ := K.h / (2 * Real.pi)

/-- Fine-structure constant `α = (1 / (4π ε₀)) · e² / (ħ c)`. -/
noncomputable def fineStructure : ℝ :=
  1 / (4 * Real.pi * K.ε0) * (K.e ^ 2 / (hbar K * K.c))

/-- Compton wavelength of the electron `λₑ = h / (mₑ c)`. -/
noncomputable def comptonWavelength : ℝ := K.h / (K.me * K.c)

/-- Compton frequency of the electron `f_C = mₑ c² / h`. -/
noncomputable def comptonFrequency : ℝ := K.me * K.c ^ 2 / K.h

/-- Compton angular frequency of the electron `ω_C = 2π f_C`. -/
noncomputable def comptonAngularFrequency : ℝ := 2 * Real.pi * comptonFrequency K

/-- Bohr radius `a₀ = 4π ε₀ ħ² / (e² mₑ)`. -/
noncomputable def bohrRadius : ℝ :=
  4 * Real.pi * K.ε0 * hbar K ^ 2 / (K.e ^ 2 * K.me)

/-- Classical electron radius `rₑ = (1 / (4π ε₀)) · e² / (mₑ c²)`. -/
noncomputable def classicalElectronRadius : ℝ :=
  1 / (4 * Real.pi * K.ε0) * (K.e ^ 2 / (K.me * K.c ^ 2))

/-- Rydberg unit of energy `Ry = h c R∞`. -/
noncomputable def rydbergEnergy : ℝ := K.h * K.c * rydbergInf K

/-- Reduced mass of an electron and a nucleus of mass `M`: `μ = 1 / (1/mₑ + 1/M)`. -/
noncomputable def reducedMass (M : ℝ) : ℝ := 1 / (1 / K.me + 1 / M)

/-- Rydberg constant corrected for a nucleus of mass `M`: `R_M = (μ / mₑ) R∞`. -/
noncomputable def rydbergM (M : ℝ) : ℝ := reducedMass K M / K.me * rydbergInf K

/-- Bohr-model circular orbit of a particle of mass `m` and charge `-e` about a fixed
point charge `+e`, with principal quantum number `n`: radius `r > 0`, speed `v > 0`,
Coulomb force equal to centripetal force, and angular momentum `m v r = n ħ`. -/
def IsBohrOrbit (m : ℝ) (n : ℕ) (r v : ℝ) : Prop :=
  0 < r ∧ 0 < v ∧
  m * v ^ 2 / r = K.e ^ 2 / (4 * Real.pi * K.ε0 * r ^ 2) ∧
  m * v * r = (n : ℝ) * hbar K

/-- Total (kinetic + Coulomb potential) energy of such an orbit:
`E = m v² / 2 - e² / (4π ε₀ r)`. -/
noncomputable def orbitEnergy (m r v : ℝ) : ℝ :=
  m * v ^ 2 / 2 - K.e ^ 2 / (4 * Real.pi * K.ε0 * r)

end RydbergConstant


