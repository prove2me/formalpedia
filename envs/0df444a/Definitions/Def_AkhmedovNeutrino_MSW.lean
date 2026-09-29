-- Prove2me | Definitions.Def_AkhmedovNeutrino_MSW
-- name    : AkhmedovNeutrino_MSW
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-24T15:58:34.357204+00:00
-- url     : https://prove2.me/theorems/2ed48e6a-f5b4-4c8a-9c7e-21cba6bb41e9
-- title:
--   Two-flavour MSW Hamiltonian, energy gap, oscillation length and amplitude in matter (Akhmedov, eqs. (61), (87), (91), (94), (96), (97))
-- statement:
--   Definitions for two-flavour ($\nu_e,\nu_\mu$) neutrino oscillations in matter of constant density, following Akhmedov's lectures. Let $\Delta m^2=m_2^2-m_1^2$, $E$ the neutrino energy, $\theta_0$ the vacuum mixing angle, $G_F$ the Fermi constant and $N_e$ the electron number density, all real. Write $a=\Delta m^2/(2E)$.
--
--   1. **Charged-current potential** (eq. (87)): $V_{CC}=\sqrt2\,G_F N_e$.
--   2. **MSW Hamiltonian** (eq. (91)), in the flavour basis $(\nu_e,\nu_\mu)$:
--   $$H=\begin{pmatrix}-\frac{\Delta m^2}{4E}\cos2\theta_0+V_{CC} & \frac{\Delta m^2}{4E}\sin2\theta_0\\ \frac{\Delta m^2}{4E}\sin2\theta_0 & \frac{\Delta m^2}{4E}\cos2\theta_0\end{pmatrix}.$$
--   3. **Energy gap in matter** (eq. (94)): $\Delta_m=\sqrt{(a\cos2\theta_0-V_{CC})^2+a^2\sin^22\theta_0}$.
--   4. **Oscillation length in matter** (eq. (96)): $l_m=2\pi/\Delta_m$.
--   5. **Oscillation amplitude in matter** (eq. (97)):
--   $$\sin^22\theta=\frac{a^2\sin^22\theta_0}{(a\cos2\theta_0-V_{CC})^2+a^2\sin^22\theta_0}.$$
--   6. **Vacuum oscillation length** (eq. (61)): $l_{osc}=4\pi E/\Delta m^2$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** All quantities are real-valued functions of the parameters. Division follows the convention $x/0=0$, so $l_m=0$ and the amplitude is $0$ when $\Delta_m=0$, and $l_{osc}=0$ when $\Delta m^2=0$. Terms proportional to the identity (common phases, neutral-current potentials) are omitted from $H$, as in the source.
-- source:
--   E. Kh. Akhmedov, Neutrino physics, Lectures at the Trieste Summer School in Particle Physics 1999, arXiv:hep-ph/0001264v2, https://arxiv.org/abs/hep-ph/0001264, Sec. 7.1 eq. (61); Sec. 8.1 eqs. (87), (91); Sec. 8.2 eqs. (94), (96), (97); pp. 21, 29-31

import Mathlib

namespace AkhmedovNeutrino

/-- Charged-current matter-induced potential of the electron neutrino,
`V_CC = √2 G_F N_e` (Akhmedov, hep-ph/0001264, eq. (87)). -/
noncomputable def ccPotential (GF Ne : ℝ) : ℝ :=
  Real.sqrt 2 * GF * Ne

/-- The effective two-flavour Hamiltonian of the `(ν_e, ν_μ)` system in matter,
written in the flavour basis, with all terms proportional to the identity removed
(Akhmedov, eq. (91)). `Δm2 = m₂² - m₁²`, `E` is the neutrino energy, `θ0` is the
vacuum mixing angle, `GF` is the Fermi constant and `Ne` the electron number density. -/
noncomputable def mswHamiltonian (Δm2 E θ0 GF Ne : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-(Δm2 / (4 * E)) * Real.cos (2 * θ0) + ccPotential GF Ne,
      Δm2 / (4 * E) * Real.sin (2 * θ0);
     Δm2 / (4 * E) * Real.sin (2 * θ0),
      Δm2 / (4 * E) * Real.cos (2 * θ0)]

/-- Difference of the neutrino eigenenergies in matter,
`√((Δm²/2E · cos 2θ₀ - √2 G_F N_e)² + (Δm²/2E)² sin² 2θ₀)` (Akhmedov, eq. (94)). -/
noncomputable def matterEnergyGap (Δm2 E θ0 GF Ne : ℝ) : ℝ :=
  Real.sqrt ((Δm2 / (2 * E) * Real.cos (2 * θ0) - ccPotential GF Ne) ^ 2
    + (Δm2 / (2 * E)) ^ 2 * Real.sin (2 * θ0) ^ 2)

/-- Oscillation length in matter, `l_m = 2π / (E_A - E_B)` (Akhmedov, eq. (96)). -/
noncomputable def matterOscLength (Δm2 E θ0 GF Ne : ℝ) : ℝ :=
  2 * Real.pi / matterEnergyGap Δm2 E θ0 GF Ne

/-- Oscillation amplitude in matter, `sin² 2θ`, as the explicit resonance-shaped
expression of Akhmedov, eq. (97). -/
noncomputable def matterOscAmplitude (Δm2 E θ0 GF Ne : ℝ) : ℝ :=
  (Δm2 / (2 * E)) ^ 2 * Real.sin (2 * θ0) ^ 2 /
    ((Δm2 / (2 * E) * Real.cos (2 * θ0) - ccPotential GF Ne) ^ 2
      + (Δm2 / (2 * E)) ^ 2 * Real.sin (2 * θ0) ^ 2)

/-- Vacuum oscillation length `l_osc = 4πE / Δm²` (Akhmedov, eq. (61)). -/
noncomputable def vacuumOscLength (Δm2 E : ℝ) : ℝ :=
  4 * Real.pi * E / Δm2

end AkhmedovNeutrino


