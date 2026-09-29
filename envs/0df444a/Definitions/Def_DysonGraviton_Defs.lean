-- Prove2me | Definitions.Def_DysonGraviton_Defs
-- name    : DysonGraviton_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T23:10:16.727368+00:00
-- url     : https://prove2.me/theorems/ded4a55f-2282-421b-bc5a-2bfe2e8bb3d7
-- title:
--   Dyson 2013 — quadrupole factor $Q$, s-state, Planck length, mixing and coherence lengths
-- statement:
--   Definitions for the mission, all in the namespace `DysonGraviton`.
--
--   - **Half plane** $H = \{(s,z) : s > 0\}$.
--   - **Radial derivative** $f'(s,z) = \partial f/\partial s$.
--   - **Quadrupole factor** (Eq. (16)):
--   $$Q(f) = \frac{\int_H s^3 [f'(s,z)]^2 \, d(s,z)}{2\int_H s\, f(s,z)^2\, d(s,z)}.$$
--   - **s-state** (Eq. (19)): $f(s,z) = r^{-n} e^{-r/R}$, $r = \sqrt{s^2+z^2}$.
--   - **Planck length** (Eq. (5)): $L_p = \sqrt{G\hbar/c^3}$.
--   - **Gravitational-wave energy density** (Eq. (2)): $E = \frac{c^2}{32\pi G}\,\omega^2 f^2$.
--   - **Single-graviton energy density bound** (Eq. (3)): $E_s = \hbar\omega^4/c^3$.
--   - **Mixing length** (Eq. (29)): $L = 2c^2/(\sqrt G\, B)$.
--   - **Conversion probability** (Eq. (28)): $P = \sin^2(D/L)$.
--   - **Photon slowdown** (Eq. (36)): $g = k\alpha B^2/(360\pi^2H_c^2)$.
--   - **Coherence length** (Eq. (37)): $L_c = c/(g\omega)$.
-- source:
--   F. Dyson, Is a Graviton Detectable?, Int. J. Mod. Phys. A 28 (2013) 1330041, https://doi.org/10.1142/S0217751X1330041X, Eqs. (2), (3), (5), (16), (19), (28), (29), (36), (37)

import Mathlib

/-!
# Dyson (2013), "Is a graviton detectable?" — definitions

Definitions used by the Prove2Me mission proposal drafted from
F. Dyson, Int. J. Mod. Phys. A 28 (2013) 1330041.
-/

namespace DysonGraviton

/-- The half plane `{(s, z) : s > 0}` of cylindrical coordinates
(`s` = distance from the `z`-axis). -/
def halfPlane : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.univ

/-- The partial derivative `f' = ∂f/∂s` of a function `f(s, z)`. -/
noncomputable def dS (f : ℝ → ℝ → ℝ) (s z : ℝ) : ℝ :=
  deriv (fun t => f t z) s

/-- Numerator of Eq. (16): `∫∫ s³ [f']² ds dz` over `s > 0`, `z ∈ ℝ`. -/
noncomputable def numQ (f : ℝ → ℝ → ℝ) : ℝ :=
  ∫ p in halfPlane, p.1 ^ 3 * (dS f p.1 p.2) ^ 2

/-- The integral `∫∫ s [f]² ds dz` over `s > 0`, `z ∈ ℝ` (Eq. (16)). -/
noncomputable def denQ (f : ℝ → ℝ → ℝ) : ℝ :=
  ∫ p in halfPlane, p.1 * (f p.1 p.2) ^ 2

/-- Dyson's quadrupole factor, Eq. (16):
`Q = (∫∫ s³ [f']² ds dz) / (2 ∫∫ s [f]² ds dz)`. -/
noncomputable def Q (f : ℝ → ℝ → ℝ) : ℝ :=
  numQ f / (2 * denQ f)

/-- The s-state wave function of Eq. (19), `f = r⁻ⁿ exp(-r/R)` with
`r = √(s² + z²)`, written in cylindrical coordinates `(s, z)`. -/
noncomputable def sState (n R : ℝ) (s z : ℝ) : ℝ :=
  Real.sqrt (s ^ 2 + z ^ 2) ^ (-n) * Real.exp (-(Real.sqrt (s ^ 2 + z ^ 2)) / R)

/-- The Planck length, Eq. (5): `L_p = (G ħ / c³)^{1/2}`. -/
noncomputable def planckLength (G hbar c : ℝ) : ℝ :=
  Real.sqrt (G * hbar / c ^ 3)

/-- Energy density of a gravitational wave of strain amplitude `f` and
angular frequency `ω`, Eq. (2): `E = (c² / (32 π G)) ω² f²`. -/
noncomputable def gwEnergyDensity (c G ω f : ℝ) : ℝ :=
  c ^ 2 / (32 * Real.pi * G) * ω ^ 2 * f ^ 2

/-- Upper bound for the energy density of a single graviton, Eq. (3):
`E_s = ħ ω⁴ / c³`. -/
noncomputable def singleGravitonEnergyDensity (hbar ω c : ℝ) : ℝ :=
  hbar * ω ^ 4 / c ^ 3

/-- Photon–graviton mixing length, Eq. (29): `L = 2c² / (G^{1/2} B)`. -/
noncomputable def mixingLength (G B c : ℝ) : ℝ :=
  2 * c ^ 2 / (Real.sqrt G * B)

/-- Gertsenshtein conversion probability, Eq. (28): `P = sin²(D / L)`. -/
noncomputable def conversionProb (G B c D : ℝ) : ℝ :=
  Real.sin (D / mixingLength G B c) ^ 2

/-- Fractional reduction of the photon velocity, Eq. (36):
`g = k α B² / (360 π² H_c²)`. -/
noncomputable def photonSlowdown (k α B Hc : ℝ) : ℝ :=
  k * α * B ^ 2 / (360 * Real.pi ^ 2 * Hc ^ 2)

/-- Coherence length, first expression in Eq. (37): `L_c = c / (g ω)`,
with `g` from Eq. (36) for polarization coefficient `k`. -/
noncomputable def coherenceLength (k α B Hc c ω : ℝ) : ℝ :=
  c / (photonSlowdown k α B Hc * ω)

end DysonGraviton


