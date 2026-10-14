-- Prove2me | Definitions.Def_GoodmanWitten_basic
-- name    : GoodmanWitten_basic
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T12:50:20.518605+00:00
-- url     : https://prove2.me/theorems/ed8b076e-c3ca-474c-8f72-a8c9447e253b
-- title:
--   Goodman–Witten (1985): units, constants and scattering model
-- statement:
--   This file fixes the physical model, units and constants used by every statement of the mission, following Goodman–Witten (1985).
--
--   **Units.** Masses and energies are in GeV with $c=1$; in kinematic statements velocities are fractions of $c$. In rate statements velocities are in cm/s, mass densities in g/cm$^3$, cross sections in cm$^2$, and squared amplitudes in GeV$^{-4}$, converted to cm$^2$ with $(\hbar c)^2$. Rates are in events per kilogram of detector per day.
--
--   **Constants.** $c = 2.99792458\times10^{10}$ cm/s; $1\ \mathrm{GeV}/c^2 = 1.78266192\times10^{-24}$ g; $\hbar c = 1.97326980\times10^{-14}$ GeV cm; $G_F = 1.1663787\times10^{-5}$ GeV$^{-2}$; $\alpha = 1/137.036$; nucleon mass $m_N = 0.9383$ GeV; a nucleus of mass number $A$ has mass $M = A\,m_N$.
--
--   **Objects.**
--   1. Recoil bounds (p. 3059): the recoil momentum bound $2mv$ and recoil-energy bound $\epsilon(m,M,v) = (2mv)^2/2M$.
--   2. Counting rate (p. 3060): $K = 6.0\times10^{26}/A$ target nuclei per kg, flux $F=\rho v/m$, and $R = KF\sigma$ (converted to events/kg/day); the reduced cross section $\bar\sigma = (\sigma/A)(1\ \mathrm{GeV}/m)$.
--   3. Elastic cross section for a constant invariant amplitude: $\sigma = \dfrac{m^2M^2}{\pi(m+M)^2}|\mathcal M|^2$.
--   4. Coherent weak scattering: $\bar N = N-(1-4\sin^2\theta)Z$ and $\mathcal M = G_F\bar Y\bar N/\sqrt2$.
--   5. Photino scattering: $q^2 = Q^2\cdot4\pi\alpha$ and $\langle|\mathcal M|^2\rangle = (4q^4/M_{\tilde Q}^4)\lambda^2J(J+1)$.
--   6. Strongly interacting particles (p. 3062): $R_{\mathrm{nuc}} = 1.25A^{1/3}\times10^{-13}$ cm, $\sigma = 4\pi R_{\mathrm{nuc}}^2$, and the rate multiplied by the stopping factor $\epsilon$.
--
--   **Formalization Note** The paper writes $M\simeq A$ GeV; the nucleon mass $0.9383$ GeV is used instead, which reproduces the paper's printed coefficients in Eqs. (2) and (3) to within a few percent. The value $6.0\times10^{26}/A$ is copied from the paper. Physical constants are modern CODATA/PDG values.
-- source:
--   M. W. Goodman and E. Witten, Detectability of certain dark-matter candidates, Phys. Rev. D 31, 3059-3063 (1985), https://doi.org/10.1103/PhysRevD.31.3059, pp. 3059-3062 (definitions accompanying Eqs. (1)-(6))

import Mathlib

/-!
# Goodman–Witten (1985): basic physical model

Source: M. W. Goodman and E. Witten, *Detectability of certain dark-matter candidates*,
Phys. Rev. D 31, 3059–3063 (1985), https://doi.org/10.1103/PhysRevD.31.3059.

Units and conventions used throughout the mission:
* masses and energies are in GeV (natural units, `c = 1`);
* velocities in the kinematic statements are dimensionless (fractions of `c`);
* velocities in event-rate statements are in cm/s, mass densities in g/cm³,
  cross sections in cm²;
* squared invariant amplitudes are in GeV⁻⁴ and are converted to cm² with `(ħc)²`;
* event rates are in events per kilogram of detector per day.
-/

namespace GoodmanWitten

/-! ## Physical constants -/

/-- Speed of light in cm/s. -/
noncomputable def speedOfLight : ℝ := 2.99792458e10

/-- Mass of `1 GeV/c²` expressed in grams. -/
noncomputable def gramsPerGeV : ℝ := 1.78266192e-24

/-- `ħc` in GeV·cm (converts GeV⁻² to cm²). -/
noncomputable def hbarc : ℝ := 1.97326980e-14

/-- The Fermi constant `G_F` in GeV⁻². -/
noncomputable def fermiConstant : ℝ := 1.1663787e-5

/-- The fine-structure constant `α`. -/
noncomputable def fineStructure : ℝ := 1 / 137.036

/-- Nucleon mass in GeV; a nucleus of mass number `A` has mass `A` times this. -/
noncomputable def nucleonMass : ℝ := 0.9383

/-- Seconds per day. -/
noncomputable def secondsPerDay : ℝ := 86400

/-- Mass (GeV) of a target nucleus of mass number `A`. -/
noncomputable def nucleusMass (A : ℝ) : ℝ := A * nucleonMass

/-! ## Kinematics (p. 3059) -/

/-- The paper's bound `2 m v` on the recoil momentum given to a nucleus by a halo particle
of mass `m` and speed `v`. -/
def maxRecoilMomentum (m v : ℝ) : ℝ := 2 * m * v

/-- The paper's bound `ε = (2 m v)² / (2 M)` on the recoil kinetic energy of a nucleus of
mass `M` hit by a halo particle of mass `m` and speed `v`. -/
noncomputable def maxRecoilEnergy (m M v : ℝ) : ℝ := (2 * m * v) ^ 2 / (2 * M)

/-! ## Counting rate (p. 3060, Eq. (1)) -/

/-- Number of target nuclei in one kilogram of detector made of nuclei of mass number `A`:
`K = 6.0 × 10²⁶ / A`. -/
noncomputable def targetNucleiPerKg (A : ℝ) : ℝ := 6.0e26 / A

/-- Counting rate `R = K F σ` (events per kg per day) for halo particles of mass `m` (GeV),
mass density `ρ` (g/cm³), mean velocity `v` (cm/s) and cross section `σ` (cm²) on nuclei of
mass number `A`; the flux is `F = ρ v / m`. -/
noncomputable def eventRatePerKgDay (A σ ρ v m : ℝ) : ℝ :=
  targetNucleiPerKg A * (ρ / (m * gramsPerGeV)) * v * σ * secondsPerDay

/-- The paper's reduced cross section `σ̄ = (σ / A)(1 GeV / m)`, with `m` in GeV. -/
noncomputable def reducedCrossSection (A σ m : ℝ) : ℝ := σ / A * (1 / m)

/-- Elastic cross section `σ = [m² M² / π (m + M)²] |𝓜|²` for a constant invariant amplitude,
converted to cm²; `ampSq = |𝓜|²` is in GeV⁻⁴, masses in GeV. -/
noncomputable def elasticCrossSection (m M ampSq : ℝ) : ℝ :=
  m ^ 2 * M ^ 2 / (Real.pi * (m + M) ^ 2) * ampSq * hbarc ^ 2

/-! ## (i) Coherent weak interactions (p. 3060) -/

/-- Effective neutron number `N̄ = N − (1 − 4 sin²θ) Z` of a nucleus with `N` neutrons and
`Z` protons; `s = sin²θ` is the weak mixing angle. -/
def effectiveNeutronNumber (N Z s : ℝ) : ℝ := N - (1 - 4 * s) * Z

/-- `|𝓜|²` for the coherent weak amplitude `𝓜 = G_F Ȳ N̄ / √2`. -/
noncomputable def coherentAmpSq (Ybar Nbar : ℝ) : ℝ :=
  fermiConstant ^ 2 * Ybar ^ 2 * Nbar ^ 2 / 2

/-- Coherent weak cross section (cm²): `σ = [m² M² / 2π (m + M)²] G_F² Ȳ² N̄²`. -/
noncomputable def coherentCrossSection (m M Ybar Nbar : ℝ) : ℝ :=
  elasticCrossSection m M (coherentAmpSq Ybar Nbar)

/-! ## (ii) Spin-dependent interactions: photinos (p. 3061) -/

/-- Square `q²` of the charge `q = Q e` of a quark with charge `Q` in units of `e`, using
`e² = 4πα` (natural units). -/
noncomputable def quarkChargeSq (Q : ℝ) : ℝ := Q ^ 2 * (4 * Real.pi * fineStructure)

/-- Spin-averaged `⟨|𝓜|²⟩ = (4 q⁴ / M_Q̃⁴) λ² J(J+1)` for photino–nucleus scattering;
`MQ` is the common scalar-quark mass (GeV) and `lamJJ = λ² J(J+1)`. -/
noncomputable def photinoAmpSq (Q MQ lamJJ : ℝ) : ℝ :=
  4 * quarkChargeSq Q ^ 2 / MQ ^ 4 * lamJJ

/-- Spin-dependent photino–nucleus cross section (cm²). -/
noncomputable def photinoCrossSection (m M Q MQ lamJJ : ℝ) : ℝ :=
  elasticCrossSection m M (photinoAmpSq Q MQ lamJJ)

/-! ## (iii) Strongly interacting particles (p. 3062) -/

/-- Nuclear radius `R = 1.25 A^{1/3} × 10⁻¹³ cm`. -/
noncomputable def nuclearRadius (A : ℝ) : ℝ := 1.25 * A ^ ((1 : ℝ) / 3) * 1e-13

/-- Low-energy hard-sphere cross section `σ = 4π R²` (cm²). -/
noncomputable def strongCrossSection (A : ℝ) : ℝ := 4 * Real.pi * nuclearRadius A ^ 2

/-- Counting rate for strongly interacting particles of mass `MX`, including the stopping
factor `ε` of the earth or atmosphere. -/
noncomputable def strongEventRate (A MX ε ρ v : ℝ) : ℝ :=
  ε * eventRatePerKgDay A (strongCrossSection A) ρ v MX

end GoodmanWitten


