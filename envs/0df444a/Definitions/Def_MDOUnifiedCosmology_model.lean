-- Prove2me | Definitions.Def_MDOUnifiedCosmology_model
-- name    : MDOUnifiedCosmology_model
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T13:26:38.68399+00:00
-- url     : https://prove2.me/theorems/3626f691-e67a-4313-92be-714143754648
-- title:
--   Unified MDO-field cosmology: Friedmann system, potentials, density parameters
-- statement:
--   Throughout, $\kappa^2 = 8\pi G$ (units $c=\hbar=1$), $a(t)>0$ is the scale factor of the flat FLRW metric, $H=\dot a/a$ is the Hubble function, $\phi(t)$ is the time-dependent part of the MDO fermionic field, $V$ is its potential, $\rho_m, p_m$ are the energy density and pressure of the other matter components, and $F(\phi) = 1+\kappa^2\phi^2/8$.
--
--   This file fixes the model of Pereira, Alves and Guimarães (2019), Sect. 2–4, with all quantities real functions of cosmic time (lapse $N=1$):
--
--   1. **Hubble function** $H=\dot a/a$ and **coupling factor** $F(\phi)=1+\kappa^2\phi^2/8$.
--   2. **MDO energy density and pressure**, Eqs. (10)–(11):
--   $$\rho_\phi=\frac{\dot\phi^2}{2}+V(\phi)+\frac38\frac{H^2\phi^2}{F},\qquad p_\phi=\frac{\dot\phi^2}{2}-V(\phi)-\frac38\frac{H^2\phi^2}{F}-\frac14\frac{\dot H\phi^2}{F}-\frac12\frac{H\phi\dot\phi}{F^2}.$$
--   3. **Dynamical equations** as predicates at a time $t$: the Friedmann equations (5) and (6), the field equation (7), the matter conservation equation (9) and the MDO conservation equation (14).
--   4. **Potentials** $V_1(\phi)=A^4(1-\phi^2/\phi_c^2)^2$, $V_2(\phi)=\frac12m^2\phi^2+\frac\alpha4\phi^4$, $V=V_1+V_2$ (Eqs. (17)–(19)), the effective mass $m_{\mathrm{eff}}^2=m^2-4A^4/\phi_c^2$ and coupling $\tilde\alpha=\alpha+4A^4/\phi_c^4$ (Eq. (20)), and $\phi_{\min}$ (Eq. (21)).
--   5. The **deceleration parameter** $q=-\ddot a a/\dot a^2$ (Eq. (31)).
--   6. **Cosmological parameters** (Sect. 3, footnote 2): $\rho_{\mathrm{crit},0}=3H_0^2/\kappa^2$, $\Omega_b=\rho_{b,0}/\rho_{\mathrm{crit},0}$, $\Omega_{DM,\phi}=\frac{\kappa^2\phi_c^2}{8}\Omega_b$, $\Lambda_{\mathrm{eff}}=\kappa^2F(\phi_c)V_2(\phi_c)$, $\Omega_{\Lambda,\phi}=\Lambda_{\mathrm{eff}}/(\kappa^2\rho_{\mathrm{crit},0})$.
--
--   **Formalization Note** Time derivatives are Mathlib's `deriv`, which returns $0$ at points of non-differentiability; theorems using these definitions carry the differentiability hypotheses they need. The torsion function $h(t)$ of Eq. (8) is already eliminated in Eqs. (5)–(7) and is not defined separately.
-- source:
--   S. H. Pereira, M. E. S. Alves, T. M. Guimarães, "An unified cosmological evolution driven by a mass dimension one fermionic field", Eur. Phys. J. C 79 (2019) 543, https://doi.org/10.1140/epjc/s10052-019-7036-5, pp. 2–5 and 7, Eqs. (5)–(11), (14), (17)–(21), (24)–(26), (31), footnote 2

import Mathlib

/-!
# Unified cosmology driven by a mass dimension one (MDO) fermionic field

Model layer for S. H. Pereira, M. E. S. Alves, T. M. Guimarães,
"An unified cosmological evolution driven by a mass dimension one fermionic field",
Eur. Phys. J. C 79 (2019) 543, https://doi.org/10.1140/epjc/s10052-019-7036-5.

Units `c = ħ = 1`, `κ² = 8πG`. All quantities are real functions of cosmic time `t`
(lapse `N = 1`, flat FLRW metric). `a` is the scale factor, `φ` the temporal part of the
MDO field, `ρm`, `pm` the energy density and pressure of the other matter components.
-/

namespace MDOUnifiedCosmology

/-- Hubble function `H = ȧ / a`. -/
noncomputable def hubble (a : ℝ → ℝ) (t : ℝ) : ℝ := deriv a t / a t

/-- The torsion/spin coupling factor `1 + κ²φ²/8` appearing throughout Eqs. (5)–(13). -/
noncomputable def couplingFactor (κ φ : ℝ) : ℝ := 1 + κ ^ 2 * φ ^ 2 / 8

/-- Energy density of the MDO field, Eq. (10). -/
noncomputable def rhoPhi (κ : ℝ) (V : ℝ → ℝ) (a φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv φ t ^ 2 / 2 + V (φ t)
    + 3 / 8 * (hubble a t ^ 2 * φ t ^ 2 / couplingFactor κ (φ t))

/-- Pressure of the MDO field, Eq. (11). -/
noncomputable def pPhi (κ : ℝ) (V : ℝ → ℝ) (a φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv φ t ^ 2 / 2 - V (φ t)
    - 3 / 8 * (hubble a t ^ 2 * φ t ^ 2 / couplingFactor κ (φ t))
    - 1 / 4 * (deriv (hubble a) t * φ t ^ 2 / couplingFactor κ (φ t))
    - 1 / 2 * (hubble a t * φ t * deriv φ t / couplingFactor κ (φ t) ^ 2)

/-- First Friedmann equation, Eq. (5), at time `t`. -/
def FriedmannEq (κ : ℝ) (V : ℝ → ℝ) (a φ ρm : ℝ → ℝ) (t : ℝ) : Prop :=
  hubble a t ^ 2 = κ ^ 2 / 3 * couplingFactor κ (φ t) * (deriv φ t ^ 2 / 2 + V (φ t) + ρm t)

/-- Second Friedmann (acceleration) equation, Eq. (6), at time `t`. -/
def AccelerationEq (κ : ℝ) (a φ ρm pm : ℝ → ℝ) (t : ℝ) : Prop :=
  deriv (hubble a) t = -(κ ^ 2 / 2) * couplingFactor κ (φ t) *
    (deriv φ t ^ 2 - 1 / 2 * (hubble a t * φ t * deriv φ t / couplingFactor κ (φ t) ^ 2)
      + ρm t + pm t)

/-- Dynamic equation of the MDO field, Eq. (7), at time `t`. -/
def FieldEq (κ : ℝ) (V : ℝ → ℝ) (a φ : ℝ → ℝ) (t : ℝ) : Prop :=
  deriv (deriv φ) t + 3 * hubble a t * deriv φ t + deriv V (φ t)
    - 3 / 4 * (hubble a t ^ 2 * φ t / couplingFactor κ (φ t) ^ 2) = 0

/-- Perfect-fluid conservation equation for the other matter components, Eq. (9). -/
def MatterConservation (a ρm pm : ℝ → ℝ) (t : ℝ) : Prop :=
  deriv ρm t + 3 * hubble a t * (ρm t + pm t) = 0

/-- Conservation equation for the MDO fluid, Eq. (14). -/
def MDOConservation (κ : ℝ) (V : ℝ → ℝ) (a φ : ℝ → ℝ) (t : ℝ) : Prop :=
  deriv (fun s => rhoPhi κ V a φ s) t
    + 3 * hubble a t * (rhoPhi κ V a φ t + pPhi κ V a φ t) = 0

/-- Symmetry breaking potential `V₁(φ) = A⁴ (1 - φ²/φc²)²`, Eq. (17). -/
noncomputable def V1 (A φc : ℝ) (φ : ℝ) : ℝ := A ^ 4 * (1 - φ ^ 2 / φc ^ 2) ^ 2

/-- Mass plus quartic self-interaction potential `V₂(φ) = m²φ²/2 + αφ⁴/4`, Eq. (18). -/
noncomputable def V2 (m α : ℝ) (φ : ℝ) : ℝ := 1 / 2 * m ^ 2 * φ ^ 2 + α / 4 * φ ^ 4

/-- The full potential of the model `V = V₁ + V₂`, Eq. (19). -/
noncomputable def potential (A φc m α : ℝ) (φ : ℝ) : ℝ := V1 A φc φ + V2 m α φ

/-- Effective squared mass `m_eff² = m² - 4A⁴/φc²`, Eq. (20). -/
noncomputable def effMassSq (A φc m : ℝ) : ℝ := m ^ 2 - 4 * A ^ 4 / φc ^ 2

/-- Effective self-coupling `α̃ = α + 4A⁴/φc⁴`, Eq. (20). -/
noncomputable def effCoupling (A φc α : ℝ) : ℝ := α + 4 * A ^ 4 / φc ^ 4

/-- Location of the minimum of the potential, Eq. (21). -/
noncomputable def phiMin (A φc m α : ℝ) : ℝ :=
  φc * Real.sqrt ((1 - m ^ 2 * φc ^ 2 / (4 * A ^ 4)) / (1 + α * φc ^ 4 / (4 * A ^ 4)))

/-- Deceleration parameter `q = -ä a / ȧ²`, Eq. (31). -/
noncomputable def decelerationParam (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(deriv (deriv a) t * a t) / deriv a t ^ 2

/-- Present critical density `ρ_crit,0 = 3H₀²/κ²` (footnote 2). -/
noncomputable def critDensity (κ H₀ : ℝ) : ℝ := 3 * H₀ ^ 2 / κ ^ 2

/-- Baryonic density parameter `Ω_b = ρ_b,0 / ρ_crit,0` (below Eq. (25)). -/
noncomputable def omegaB (κ H₀ ρb₀ : ℝ) : ℝ := ρb₀ / critDensity κ H₀

/-- MDO dark matter density parameter `Ω_DM,φ = (κ²φc²/8) Ω_b`, Eq. (26). -/
noncomputable def omegaDM (κ φc Ωb : ℝ) : ℝ := κ ^ 2 * φc ^ 2 / 8 * Ωb

/-- Effective cosmological constant `Λ_eff = κ² (1 + κ²φc²/8) V₂(φc)`, Eq. (24). -/
noncomputable def lambdaEff (κ φc m α : ℝ) : ℝ := κ ^ 2 * couplingFactor κ φc * V2 m α φc

/-- Dark energy density parameter `Ω_Λ,φ = Λ_eff / (κ² ρ_crit,0)` (below Eq. (26)). -/
noncomputable def omegaLambda (κ H₀ φc m α : ℝ) : ℝ :=
  lambdaEff κ φc m α / (κ ^ 2 * critDensity κ H₀)

end MDOUnifiedCosmology


