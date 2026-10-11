-- Prove2me | Definitions.Def_DarkEnergyLCDM_Defs
-- name    : DarkEnergyLCDM_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-11T00:57:31.552851+00:00
-- url     : https://prove2.me/theorems/27690a5c-3d61-46cb-a0a5-f329047e2470
-- title:
--   FLRW background cosmology: Friedmann, continuity and acceleration equations; density parameters; quintessence; CPL/BA; $d_L$; vacuum energy
-- statement:
--   This file contains the shared vocabulary of the mission, following §§3.1–3.8 of the source. Units have $c=1$. The scale factor is $a:\mathbb R\to\mathbb R$, and dots denote time derivatives.
--
--   1. **Hubble parameter**: $H(t) = \dot a(t)/a(t)$.
--   2. **Friedmann equation (2)** at time $t$: $H^2 = \frac{8\pi G}{3}\rho - \frac{K}{a^2} + \frac{\Lambda}{3}$.
--   3. **Continuity equation (3)** for a component $(\rho_i, p_i)$: $\dot\rho_i + 3H(\rho_i+p_i) = 0$.
--   4. **Acceleration equation (7)**: $\ddot a / a = -\frac{4\pi G}{3}(\rho+3p) + \frac{\Lambda}{3}$.
--   5. **Density parameters (6)**: $\Omega_i = \frac{8\pi G}{3H_0^2}\rho_{i0}$, $\Omega_k = -K/H_0^2$, $\Omega_\Lambda = \Lambda/(3H_0^2)$.
--   6. **ΛCDM background** on an open interval $I$. The interval is open and connected. The scale factor $a$ is $C^2$ and positive on $I$. The radiation density $\rho_r$ and the matter density $\rho_m$ are differentiable on $I$. The Friedmann equation holds on $I$ with total density $\rho_r+\rho_m$. Radiation obeys continuity with $p_r = \rho_r/3$, and matter obeys continuity with $p_m = 0$.
--   7. **Quintessence (17)**: $\rho_\phi = \dot\phi^2/2 + V(\phi)$ and $p_\phi = \dot\phi^2/2 - V(\phi)$. The equation of state is $w_\phi(\dot\phi, V) = \frac{\dot\phi^2/2 - V}{\dot\phi^2/2 + V}$.
--   8. **CPL (19)**: $w(a) = w_0 + (1-a)w_a$. **BA (20)**: $w(a) = w_0 + w_a\frac{1-a}{a^2+(1-a)^2}$.
--   9. **Luminosity distance** (formula after Eq. (11)). The comoving distance is $\chi(z) = \int_0^z d\tilde z/H(\tilde z)$, and
--   $$d_L = (1+z)\begin{cases}\dfrac{\sinh(\sqrt{\Omega_k}H_0\chi)}{H_0\sqrt{\Omega_k}}, & \Omega_k>0,\\ \chi, & \Omega_k = 0,\\ \dfrac{\sin(\sqrt{|\Omega_k|}H_0\chi)}{H_0\sqrt{|\Omega_k|}}, & \Omega_k<0.\end{cases}$$
--   10. **Cut-off vacuum energy (10)**: $\rho_{\rm vac}(k_{\lim}) = \int_{|k|\le k_{\lim}} \tfrac12\sqrt{|k|^2+m^2}\,\frac{d^3k}{(2\pi)^3}$, with $k \in \mathbb R^3$.
--
--   These definitions are reused by every theorem of the mission.
--
--   **Formalization Note** Time derivatives are Mathlib's `deriv`. The luminosity distance uses the standard convention: the source prints $1/(1+z)$ and assigns $\sin$ to $\Omega_k>0$, which conflicts with its own $\Omega_k=-K/H_0^2$. The equation of state $w_\phi$ is $p_\phi/\rho_\phi$, whereas the source's Eq. (18) prints its reciprocal. The vacuum energy includes the zero-point factor $1/2$ needed for the source's $k_{\lim}^4/(16\pi^2)$.
-- source:
--   R. von Marttens, J. Alcaniz, S. Carneiro, "A energia escura e os desafios do modelo cosmológico padrão", Cadernos de Astronomia 7(1), 62–76 (2026), https://doi.org/10.47456/Cad.Astro.v7n1.52249, pp. 63–66 and 71–72, Eqs. (2), (3), (6), (7), (10), (11), (17), (19), (20)

import Mathlib

/-!
Definitions for the mission on
R. von Marttens, J. Alcaniz, S. Carneiro,
"A energia escura e os desafios do modelo cosmológico padrão",
Cadernos de Astronomia 7(1), 62–76 (2026), DOI 10.47456/Cad.Astro.v7n1.52249.

Units with `c = 1`. Time is a real variable `t`, the scale factor is `a : ℝ → ℝ`,
and every time derivative is Mathlib's `deriv`.
-/

namespace DarkEnergyLCDM

open Real

/-- Hubble parameter `H ≡ ȧ / a` (§3.3). -/
noncomputable def hubble (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv a t / a t

/-- Friedmann equation, Eq. (2): `H² = (8πG/3) ρ − K/a² + Λ/3`,
where `ρ` is the total energy density, `K` the spatial curvature and `Λ` the
cosmological constant. -/
def FriedmannEq (G K Λ : ℝ) (a ρ : ℝ → ℝ) (t : ℝ) : Prop :=
  hubble a t ^ 2 = 8 * π * G / 3 * ρ t - K / a t ^ 2 + Λ / 3

/-- Continuity equation for one component, Eq. (3): `ρ̇ᵢ + 3H(ρᵢ + pᵢ) = 0`. -/
def ContinuityEq (a ρ p : ℝ → ℝ) (t : ℝ) : Prop :=
  deriv ρ t + 3 * hubble a t * (ρ t + p t) = 0

/-- Acceleration equation, Eq. (7): `ä/a = −(4πG/3)(ρ + 3p) + Λ/3`. -/
def AccelerationEq (G Λ : ℝ) (a ρ p : ℝ → ℝ) (t : ℝ) : Prop :=
  deriv (deriv a) t / a t = -(4 * π * G / 3) * (ρ t + 3 * p t) + Λ / 3

/-- Density parameter of a material component, Eq. (6): `Ωᵢ ≡ 8πG ρᵢ₀ / (3 H₀²)`. -/
noncomputable def densityParam (G H₀ ρ₀ : ℝ) : ℝ :=
  8 * π * G / (3 * H₀ ^ 2) * ρ₀

/-- Curvature density parameter, Eq. (6): `Ω_k ≡ −K / H₀²`. -/
noncomputable def curvatureParam (K H₀ : ℝ) : ℝ :=
  -K / H₀ ^ 2

/-- Dark-energy (cosmological-constant) density parameter, Eq. (6): `Ω_Λ ≡ Λ / (3 H₀²)`. -/
noncomputable def lambdaParam (Λ H₀ : ℝ) : ℝ :=
  Λ / (3 * H₀ ^ 2)

/-- Background ΛCDM cosmology on an open time interval `I` (§3.2–3.3):
a positive, twice continuously differentiable scale factor `a`, a radiation density
`ρr` with equation of state `w_r = 1/3` and a (baryons + CDM) matter density `ρm`
with `w_m = 0`, such that the Friedmann equation (2) holds for the total density
`ρ = ρr + ρm`, and each component obeys its own continuity equation (3). -/
structure IsLCDMBackground (G K Λ : ℝ) (I : Set ℝ) (a ρr ρm : ℝ → ℝ) : Prop where
  isOpen : IsOpen I
  isPreconnected : IsPreconnected I
  contDiff_a : ContDiffOn ℝ 2 a I
  pos_a : ∀ t ∈ I, 0 < a t
  diff_ρr : DifferentiableOn ℝ ρr I
  diff_ρm : DifferentiableOn ℝ ρm I
  friedmann : ∀ t ∈ I, FriedmannEq G K Λ a (fun s => ρr s + ρm s) t
  continuity_r : ∀ t ∈ I, ContinuityEq a ρr (fun s => ρr s / 3) t
  continuity_m : ∀ t ∈ I, ContinuityEq a ρm (fun _ => 0) t

/-- Quintessence energy density, Eq. (17): `ρ_ϕ = ϕ̇²/2 + V(ϕ)`. -/
noncomputable def quintessenceDensity (V : ℝ → ℝ) (ϕ : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv ϕ t ^ 2 / 2 + V (ϕ t)

/-- Quintessence pressure, Eq. (17): `p_ϕ = ϕ̇²/2 − V(ϕ)`. -/
noncomputable def quintessencePressure (V : ℝ → ℝ) (ϕ : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv ϕ t ^ 2 / 2 - V (ϕ t)

/-- Quintessence equation of state `w_ϕ = p_ϕ / ρ_ϕ` as a function of the kinetic
variable `ϕ̇` and the value `V` of the potential, i.e.
`w_ϕ = (ϕ̇²/2 − V)/(ϕ̇²/2 + V)` (from Eq. (17) and `wᵢ = pᵢ/ρᵢ`, §3.2). -/
noncomputable def quintessenceEOS (ϕdot V : ℝ) : ℝ :=
  (ϕdot ^ 2 / 2 - V) / (ϕdot ^ 2 / 2 + V)

/-- CPL parametrization, Eq. (19): `w(a) = w₀ + (1 − a) w_a`. -/
def cplEOS (w₀ wₐ a : ℝ) : ℝ :=
  w₀ + (1 - a) * wₐ

/-- BA parametrization, Eq. (20) (Ref. [39] of the source):
`w(a) = w₀ + w_a (1 − a)/(a² + (1 − a)²)`. -/
noncomputable def baEOS (w₀ wₐ a : ℝ) : ℝ :=
  w₀ + wₐ * ((1 - a) / (a ^ 2 + (1 - a) ^ 2))

/-- Comoving radial distance `χ(z) = ∫₀^z dz̃ / H(z̃)` for a Hubble rate `H` given as a
function of redshift (§3.5.1). -/
noncomputable def comovingDistance (H : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ z' in (0 : ℝ)..z, 1 / H z'

/-- Luminosity distance (§3.5.1, the formula below Eq. (11)), in the standard convention
`d_L = (1 + z) S_k(χ)`, where `χ` is the comoving distance and
`S_k(χ) = sinh(√Ω_k H₀ χ)/(H₀ √Ω_k)` for `Ω_k > 0`, `S_k(χ) = χ` for `Ω_k = 0`,
`S_k(χ) = sin(√|Ω_k| H₀ χ)/(H₀ √|Ω_k|)` for `Ω_k < 0`. -/
noncomputable def luminosityDistance (H : ℝ → ℝ) (H₀ Ωk z : ℝ) : ℝ :=
  (1 + z) *
    if 0 < Ωk then
      Real.sinh (Real.sqrt Ωk * H₀ * comovingDistance H z) / (H₀ * Real.sqrt Ωk)
    else if Ωk = 0 then
      comovingDistance H z
    else
      Real.sin (Real.sqrt |Ωk| * H₀ * comovingDistance H z) / (H₀ * Real.sqrt |Ωk|)

/-- Vacuum energy density with a momentum cutoff `k_lim`, Eq. (10), including the
zero-point factor `1/2`:
`ρ_vac(k_lim) = ∫_{|k| ≤ k_lim} (1/2) √(|k|² + m²) d³k / (2π)³`. -/
noncomputable def vacuumEnergyCutoff (m klim : ℝ) : ℝ :=
  ∫ k in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) klim,
    (1 / 2) * Real.sqrt (‖k‖ ^ 2 + m ^ 2) / (2 * π) ^ 3

end DarkEnergyLCDM


