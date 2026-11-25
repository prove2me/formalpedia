-- Prove2me | Definitions.Def_Arxiv2001_06227_Basic
-- name    : Arxiv2001_06227_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T07:37:43.726188+00:00
-- url     : https://prove2.me/theorems/d2b46a5e-e1cd-4355-a4b1-29e1d79819fd
-- title:
--   Scalar-wave power densities, ensemble-average splitting and slab absorption models
-- statement:
--   Objects of Sections II.A, IV and Appendices B and D of Sheremet, Pierrat and Carminati (2020).
--
--   1. **Space and derivatives.** Fields live on $\mathbb{R}^3$. $\partial_i$ is the partial derivative along the $i$-th axis, $\Delta f=\sum_i\partial_i\partial_i f$ the Laplacian of a complex field and $\nabla\cdot J=\sum_i\partial_iJ_i$ the divergence of a real vector field.
--   2. **Scalar wave model (eqs. 4-6).** With $k_0=\omega/c$, a scattered field $E_s$ of the incident field $E_0$ in a medium of permittivity $1+\delta\epsilon$ satisfies $\Delta E_s+k_0^2E_s=-k_0^2\,\delta\epsilon\,E$, where $E=E_0+E_s$. The induced current is $j=-i\omega\epsilon_0\,\delta\epsilon\,E$.
--   3. **Power densities (eqs. 51-53, Appendix B).** $\mathcal{P}_e=\tfrac12\operatorname{Re}[jE_0^*]$, $\mathcal{P}_a=\tfrac12\operatorname{Re}[jE^*]$, $\mathcal{P}_s=\nabla\cdot J_s$ with $J_s=\frac{1}{2\mu_0\omega}\operatorname{Im}(E_s^*\nabla E_s)$.
--   4. **Ensemble averages (Section IV.A).** Realizations of disorder are points $\xi$ of a probability space with law $P$; $\langle X\rangle(r)=\int X_\xi(r)\,dP(\xi)$ and $\delta X=X-\langle X\rangle$. Then $\langle\mathcal{P}_{e,a,s}\rangle$ are the averages of the densities of item 3, $\overline{\mathcal{P}}_e=\tfrac12\operatorname{Re}[\langle j\rangle E_0^*]$, $\overline{\mathcal{P}}_a=\tfrac12\operatorname{Re}[\langle j\rangle\langle E\rangle^*]$, $\overline{\mathcal{P}}_s$ is the scattered power density of $\langle E_s\rangle$, $\widetilde{\mathcal{P}}_a=\langle\tfrac12\operatorname{Re}[\delta j\,\delta E^*]\rangle$ and $\widetilde{\mathcal{P}}_s=\langle\nabla\cdot J_s[\delta E_s]\rangle$.
--   5. **Scattering mean free path (eq. 77).** $\frac1{\ell_s}=\frac{\rho k_0^4|\Delta\epsilon|^2}{16\pi^2}\int_{S^2}|\Theta[k_r(u'-u)]|^2\,\widetilde S[k_r(u'-u)]\,du'$, the integral taken with the surface measure of the unit sphere.
--   6. **Ballistic slab (eqs. 68, 78).** For a slab of thickness $L$ and section $S$ with ballistic specific intensity $\mathcal{I}(s)$ at depth $s$, $\overline{P}_a=\frac{v_ES}{\ell_e}\int_0^L\frac{\mathcal{I}(s)}{v_E}\,ds$.
--   7. **Single-scattering slab (Appendix D).** $\Theta$ is the Heaviside function. $p(\mu,\mu')$ is the azimuth-integrated phase function; the slice $\mu\mapsto p(\mu,1)$ is non-negative and integrable on $[-1,1]$ with integral $1$. With $\mu_e=\mu_a+\mu_s$, $R$ is given by (D1), $T$ by (D2) with $\mu\in(0,1)$, the closed form of $R+T$ by (D3), $\langle P_a\rangle=P_0[1-(R+T)]$ with $R+T$ from (D3), and the left-hand side of (D5) is $\int_0^1\big[\frac{\mu p(-\mu,1)}{1+\mu}\{1-e^{-b(1+\mu)/\mu}\}+\frac{\mu p(\mu,1)}{1-\mu}\{e^{-b}-e^{-b/\mu}\}\big]d\mu-be^{-b}$.
--
--   **Formalization Note** The energy current uses the sign of Appendix B, $\operatorname{Im}(E_s^*\nabla E_s)$; eq. (53) prints $\operatorname{Im}(E_s\nabla E_s^*)$, which has the opposite sign. In (D2) the $\mu$-integral runs over $(0,1)$; the printed limits $-1$ to $0$ do not give (D3).
-- source:
--   Sheremet, Pierrat and Carminati, Absorption of scalar waves in correlated disordered media and its maximization using stealth hyperuniformity, arXiv:2001.06227v2 (2020), Sections II.A, IV.A-IV.C, Appendices B and D

import Mathlib

/-!
A. Sheremet, R. Pierrat and R. Carminati, *Absorption of scalar waves in correlated disordered
media and its maximization using stealth hyperuniformity*, arXiv:2001.06227v2 (2020): the scalar
wave model of Section II.A, the power densities and their ensemble-average splitting of
Section IV.A and Appendix B, the structure-factor form of the scattering mean free path of
Section IV.B, the ballistic slab absorption of Section IV.C, and the single-scattering slab model
of Appendix D.
-/

open MeasureTheory

noncomputable section

namespace Arxiv2001_06227

/-- Physical space `ℝ³` (Section II.A). -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The partial derivative `∂_i f(x)` along the `i`-th coordinate axis of `ℝ³`. -/
def pd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Space → F) (i : Fin 3)
    (x : Space) : F :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

/-- The Laplacian `Δ f = ∑_i ∂_i ∂_i f` of a complex field on `ℝ³` (eqs. (4)-(6)). -/
def lap (f : Space → ℂ) (x : Space) : ℂ :=
  ∑ i, pd (pd f i) i x

/-- The divergence `∇ · J = ∑_i ∂_i J_i` of a real vector field on `ℝ³` (eq. (53)). -/
def div3 (J : Space → Fin 3 → ℝ) (x : Space) : ℝ :=
  ∑ i, pd (fun y => J y i) i x

/-- Eq. (6): `E_s` is the scattered field of the incident field `E_0` in the medium with
permittivity `1 + δε`, i.e. `Δ E_s + k_0² E_s = -k_0² δε E` with `E = E_0 + E_s` and
`k_0 = ω / c` (eq. (4)). -/
def IsScatteredField (c omega : ℝ) (deps E0 Es : Space → ℂ) : Prop :=
  ∀ x, lap Es x + (((omega / c) ^ 2 : ℝ) : ℂ) * Es x =
    -((((omega / c) ^ 2 : ℝ) : ℂ) * deps x * (E0 x + Es x))

/-- Section II.A (below eq. (2)) and Appendix B: the induced current density
`j = -i ω ε₀ δε E`. -/
def inducedCurrent (eps0 omega : ℝ) (deps E : Space → ℂ) (x : Space) : ℂ :=
  -(Complex.I * (omega : ℂ) * (eps0 : ℂ) * deps x * E x)

/-- Eq. (51): the extinguished power density `P_e = ½ Re[j E_0^*]`. -/
def extPower (j E0 : Space → ℂ) (x : Space) : ℝ :=
  (1 / 2 : ℝ) * (j x * (starRingEnd ℂ) (E0 x)).re

/-- Eq. (52): the absorbed power density `P_a = ½ Re[j E^*]`. -/
def absPower (j E : Space → ℂ) (x : Space) : ℝ :=
  (1 / 2 : ℝ) * (j x * (starRingEnd ℂ) (E x)).re

/-- Appendix B: the energy current of the scattered field,
`J_s = (1 / (2 μ₀ ω)) Im(E_s^* ∇E_s)`. -/
def energyCurrent (mu0 omega : ℝ) (Es : Space → ℂ) (x : Space) : Fin 3 → ℝ :=
  fun i => (1 / (2 * mu0 * omega)) * ((starRingEnd ℂ) (Es x) * pd Es i x).im

/-- Eq. (53): the scattered power density `P_s = ∇ · J_s`. -/
def scaPower (mu0 omega : ℝ) (Es : Space → ℂ) (x : Space) : ℝ :=
  div3 (energyCurrent mu0 omega Es) x

section Average

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Section IV.A: the ensemble average `⟨X⟩(r)` of a random field over the realizations of
disorder, with law `P`. -/
def ensAvg (P : Measure Ω) (X : Ω → Space → ℂ) (x : Space) : ℂ :=
  ∫ ξ, X ξ x ∂P

/-- Section IV.A: the fluctuation `δX = X - ⟨X⟩` of a random field. -/
def fluct (P : Measure Ω) (X : Ω → Space → ℂ) : Ω → Space → ℂ :=
  fun ξ x => X ξ x - ensAvg P X x

/-- The random total field `E = E_0 + E_s` of each realization (Section II.A). -/
def totField (E0 : Space → ℂ) (Es : Ω → Space → ℂ) : Ω → Space → ℂ :=
  fun ξ x => E0 x + Es ξ x

/-- The random induced current `j = -i ω ε₀ δε E` of each realization. -/
def randCurrent (eps0 omega : ℝ) (deps : Ω → Space → ℂ) (E0 : Space → ℂ)
    (Es : Ω → Space → ℂ) : Ω → Space → ℂ :=
  fun ξ => inducedCurrent eps0 omega (deps ξ) (totField E0 Es ξ)

/-- Section IV.A: the average extinguished power density `⟨P_e(r)⟩`. -/
def meanExtPower (P : Measure Ω) (eps0 omega : ℝ) (deps : Ω → Space → ℂ) (E0 : Space → ℂ)
    (Es : Ω → Space → ℂ) (x : Space) : ℝ :=
  ∫ ξ, extPower (randCurrent eps0 omega deps E0 Es ξ) E0 x ∂P

/-- Section IV.A: the average absorbed power density `⟨P_a(r)⟩`. -/
def meanAbsPower (P : Measure Ω) (eps0 omega : ℝ) (deps : Ω → Space → ℂ) (E0 : Space → ℂ)
    (Es : Ω → Space → ℂ) (x : Space) : ℝ :=
  ∫ ξ, absPower (randCurrent eps0 omega deps E0 Es ξ) (totField E0 Es ξ) x ∂P

/-- Section IV.A: the average scattered power density `⟨P_s(r)⟩`. -/
def meanScaPower (P : Measure Ω) (mu0 omega : ℝ) (Es : Ω → Space → ℂ) (x : Space) : ℝ :=
  ∫ ξ, scaPower mu0 omega (Es ξ) x ∂P

/-- Eq. (56): `P̄_e(r) = ½ Re[⟨j⟩ E_0^*]`, the part of `⟨P_e⟩` built from average quantities. -/
def barExtPower (P : Measure Ω) (eps0 omega : ℝ) (deps : Ω → Space → ℂ) (E0 : Space → ℂ)
    (Es : Ω → Space → ℂ) (x : Space) : ℝ :=
  extPower (ensAvg P (randCurrent eps0 omega deps E0 Es)) E0 x

/-- Eqs. (56) and (61): `P̄_a(r) = ½ Re[⟨j⟩ ⟨E^*⟩]`. -/
def barAbsPower (P : Measure Ω) (eps0 omega : ℝ) (deps : Ω → Space → ℂ) (E0 : Space → ℂ)
    (Es : Ω → Space → ℂ) (x : Space) : ℝ :=
  absPower (ensAvg P (randCurrent eps0 omega deps E0 Es)) (ensAvg P (totField E0 Es)) x

/-- Eq. (56): `P̄_s(r)`, the scattered power density of the average scattered field `⟨E_s⟩`. -/
def barScaPower (P : Measure Ω) (mu0 omega : ℝ) (Es : Ω → Space → ℂ) (x : Space) : ℝ :=
  scaPower mu0 omega (ensAvg P Es) x

/-- Eq. (56): `P̃_a(r) = ⟨½ Re[δj δE^*]⟩`, the part of `⟨P_a⟩` built from the fluctuations. -/
def tildeAbsPower (P : Measure Ω) (eps0 omega : ℝ) (deps : Ω → Space → ℂ) (E0 : Space → ℂ)
    (Es : Ω → Space → ℂ) (x : Space) : ℝ :=
  ∫ ξ, absPower (fluct P (randCurrent eps0 omega deps E0 Es) ξ)
    (fluct P (totField E0 Es) ξ) x ∂P

/-- Eq. (56): `P̃_s(r)`, the average scattered power density of the fluctuation `δE_s`. -/
def tildeScaPower (P : Measure Ω) (mu0 omega : ℝ) (Es : Ω → Space → ℂ) (x : Space) : ℝ :=
  ∫ ξ, scaPower mu0 omega (fluct P Es ξ) x ∂P

end Average

/-- Eq. (77): the inverse scattering mean free path of identical scatterers in terms of the
corrected structure factor,
`1/ℓ_s = (ρ k_0⁴ |Δε|² / (16 π²)) ∫ |Θ[k_r(u' - u)]|² S̃[k_r(u' - u)] du'`,
the integral running over the unit sphere `u'` with its surface measure; `Θhat` is the Fourier
transform of the indicator of one particle and `u` the propagation direction. -/
def invScatLength (rho k0 kr : ℝ) (deltaEps : ℂ) (thetaHat : Space → ℂ) (sTilde : Space → ℝ)
    (u : Space) : ℝ :=
  rho * k0 ^ 4 * ‖deltaEps‖ ^ 2 / (16 * Real.pi ^ 2) *
    ∫ v : Metric.sphere (0 : Space) 1,
      ‖thetaHat (kr • ((v : Space) - u))‖ ^ 2 * sTilde (kr • ((v : Space) - u))
      ∂(volume : Measure Space).toSphere

/-- Eqs. (68) and (78), slab of thickness `L` and transverse section `S` at normal incidence:
`P̄_a = (v_E / ℓ_e) ∫ Ū d³r = (v_E S / ℓ_e) ∫_0^L I(s) / v_E ds`, where `I(s)` is the ballistic
specific intensity at depth `s` and `Ū = I / v_E` the ballistic energy density (eq. (49)). -/
def slabBallisticAbsorbed (vE S ellE L : ℝ) (I : ℝ → ℝ) : ℝ :=
  vE * S / ellE * ∫ s in (0 : ℝ)..L, I s / vE

/-- Appendix D: the Heaviside step function `Θ` (its value at `0` is immaterial). -/
def heaviside (t : ℝ) : ℝ := if 0 ≤ t then 1 else 0

/-- Appendix D: `p(μ, μ')` is the phase function integrated over the azimuth, so that the slice
`μ ↦ p(μ, 1)` used in Appendix D is non-negative, integrable on `[-1, 1]` and of total mass `1`
(the phase function of eq. (47) is non-negative and normalised on the unit sphere). -/
def IsAzimuthalPhase (p : ℝ → ℝ → ℝ) : Prop :=
  (∀ μ μ', 0 ≤ p μ μ') ∧ IntegrableOn (fun μ => p μ 1) (Set.Icc (-1) 1) ∧
    ∫ μ in (-1 : ℝ)..1, p μ 1 = 1

/-- Eq. (D1): the reflected power fraction `R` of the slab in the single-scattering
approximation, with `μ_s = 1/ℓ_s`, `μ_a = 1/ℓ_a`:
`R = ∫_0^∞ μ_s e^{-μ_s s} ∫_{-1}^0 p(μ,1) ∫_0^∞ μ_s e^{-μ_s s'} e^{-μ_a (s - s/μ)}
Θ[L - s] Θ[s' + s/μ] ds' dμ ds`. -/
def slabReflect (p : ℝ → ℝ → ℝ) (muS muA L : ℝ) : ℝ :=
  ∫ s in Set.Ioi (0 : ℝ), muS * Real.exp (-(muS * s)) *
    ∫ μ in Set.Ioo (-1 : ℝ) 0, p μ 1 *
      ∫ s' in Set.Ioi (0 : ℝ), muS * Real.exp (-(muS * s')) *
        Real.exp (-(muA * (s - s / μ))) * heaviside (L - s) * heaviside (s' + s / μ)

/-- Eq. (D2), with the `μ`-integral over the forward hemisphere `0 < μ < 1` (the printed limits
`-1` to `0` are a misprint; see `REPORT.md`): the transmitted power fraction
`T = e^{-μ_e L} + ∫_0^∞ μ_s e^{-μ_s s} ∫_0^1 p(μ,1) ∫_0^∞ μ_s e^{-μ_s s'}
e^{-μ_a (s + (L - s)/μ)} Θ[L - s] Θ[s' - (L - s)/μ] ds' dμ ds`, with `μ_e = μ_a + μ_s`. -/
def slabTransmit (p : ℝ → ℝ → ℝ) (muS muA L : ℝ) : ℝ :=
  Real.exp (-((muA + muS) * L)) +
    ∫ s in Set.Ioi (0 : ℝ), muS * Real.exp (-(muS * s)) *
      ∫ μ in Set.Ioo (0 : ℝ) 1, p μ 1 *
        ∫ s' in Set.Ioi (0 : ℝ), muS * Real.exp (-(muS * s')) *
          Real.exp (-(muA * (s + (L - s) / μ))) * heaviside (L - s) *
            heaviside (s' - (L - s) / μ)

/-- Eq. (D3): the closed form of `R + T` in the single-scattering approximation, with
`μ_e = μ_a + μ_s`:
`e^{-μ_e L} + ∫_0^1 (μ_s/μ_e) (μ/(μ+1)) p(-μ,1) {1 - e^{-μ_e L (μ+1)/μ}} dμ
 + ∫_0^1 (μ_s/μ_e) (μ/(μ-1)) p(μ,1) {1 - e^{-μ_e L (μ-1)/μ}} e^{-μ_e L/μ} dμ`. -/
def slabRT (p : ℝ → ℝ → ℝ) (muS muA L : ℝ) : ℝ :=
  Real.exp (-((muA + muS) * L)) +
    (∫ μ in Set.Ioo (0 : ℝ) 1, muS / (muA + muS) * (μ / (μ + 1)) * p (-μ) 1 *
      (1 - Real.exp (-((muA + muS) * L * ((μ + 1) / μ))))) +
    ∫ μ in Set.Ioo (0 : ℝ) 1, muS / (muA + muS) * (μ / (μ - 1)) * p μ 1 *
      (1 - Real.exp (-((muA + muS) * L * ((μ - 1) / μ)))) *
        Real.exp (-((muA + muS) * L / μ))

/-- Appendix D: the average absorbed power `⟨P_a⟩ = P_0 [1 - (R + T)]` of the slab, with `R + T`
given by eq. (D3), as a function of `μ_s`, `μ_a` and `L`. -/
def slabAbsorbed (p : ℝ → ℝ → ℝ) (P0 muS muA L : ℝ) : ℝ :=
  P0 * (1 - slabRT p muS muA L)

/-- Eq. (D5): the left-hand side of the equation for the critical absorption optical thickness,
`∫_0^1 [μ p(-μ,1)/(1+μ) {1 - e^{-b(1+μ)/μ}} + μ p(μ,1)/(1-μ) {e^{-b} - e^{-b/μ}}] dμ - b e^{-b}`. -/
def criticalLHS (p : ℝ → ℝ → ℝ) (b : ℝ) : ℝ :=
  (∫ μ in Set.Ioo (0 : ℝ) 1,
    (μ * p (-μ) 1 / (1 + μ) * (1 - Real.exp (-(b * (1 + μ) / μ))) +
      μ * p μ 1 / (1 - μ) * (Real.exp (-b) - Real.exp (-(b / μ))))) - b * Real.exp (-b)

end Arxiv2001_06227


