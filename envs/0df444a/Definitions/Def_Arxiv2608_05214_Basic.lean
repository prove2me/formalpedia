-- Prove2me | Definitions.Def_Arxiv2608_05214_Basic
-- name    : Arxiv2608_05214_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T19:14:11.277795+00:00
-- url     : https://prove2.me/theorems/30b75ab9-0faa-5a6a-832b-25bed6317dd2
-- title:
--   Traveltime transformation, 1D impulse response and annihilator kernel, interface reflection, true-amplitude image and one-way decomposition
-- statement:
--   Objects of Sections II-B, III, VIII-B and Appendices A and C of Oyekan (2026).
--
--   1. **Traveltime coordinate and horn equation (Section III-B).** For a wave speed $c(x)>0$ the one-way traveltime is $\tau(x)=\int_0^x dx'/c(x')$. The left side of the 1D wave equation (14) is $\rho\,\partial_t^2u-\partial_x(\rho c^2\,\partial_xu)$. The left side of Webster's horn equation (15) is $Z\,\partial_t^2w-\partial_\tau(Z\,\partial_\tau w)$, where $Z(\tau)$ is the impedance $\rho c$ written as a function of traveltime.
--   2. **Scattering potential (eqs. 17-18).** For $\eta=\sqrt{\rho c}$ the scattering potential is $q=\eta''/\eta$, and the left side of the 1D acoustic Schrödinger equation (17) is $\partial_t^2\psi-\partial_\tau^2\psi+q(\tau)\psi$.
--   3. **Distributional solutions with a leading pulse.** A test function is a smooth, compactly supported $\chi(\tau,t)$. Write $L\chi=\partial_t^2\chi-\partial_\tau^2\chi+q(\tau)\chi$. The distribution $\psi=\delta(t-\tau)+g\,\mathbf 1_S$ solves (17) on an open set $U$ if
--   $$\int_{\mathbb R}(L\chi)(\tau,\tau)\,d\tau+\iint_S g\,L\chi\,d\tau\,dt=0$$
--   for every test function $\chi$ supported in $U$.
--   4. **Impulse response and reflection response (eqs. 19-23, A-3).** $g$ is the tail and $R$ the reflection response of the causal impulse response if: $g$ is $C^2$ on the closed half-plane $\{t\ge\tau\}$; $\psi=\delta(t-\tau)+g(\tau,t)H(t-\tau)$ solves (17) on the whole plane; for $\tau<0$ and $t\ge\tau$, $g(\tau,t)=R(t+\tau)$; and $R(t)=0$ for $t<0$. $R$ is *a reflection response of $q$* if such a $g$ exists.
--   5. **Annihilator kernel (eqs. 24, A-6, A-7).** $A(\tau,t)$ is an annihilator kernel if $A$ is $C^2$ on the closed cone $|t|\le\tau$, $\psi_a=\delta(t-\tau)+A(\tau,t)\mathbf 1_{|t|<\tau}$ solves (17) on $\tau>0$, and $A(\tau,-\tau)=0$ for $\tau\ge0$. This is the transformation-operator representation (A-6) applied to the free pulse $\psi_0(s,t)=\delta(t-s)$.
--   6. **Single interface (Section III-E).** Above an interface at traveltime $\tau_0$ the scaled field is $f(t-\tau)+r\,f(t+\tau-2\tau_0)$; below it, it is $T\,f(t-\tau)$. The interface conditions are continuity at $\tau_0$ of the displacement $u=\psi/\eta$ and of the traction $\eta^2\partial_\tau u$, with $\eta=\eta_1$ above and $\eta=\eta_2$ below.
--   7. **Illumination-compensated image (eq. 58).** For real one-way Green's functions $G^\pm(x_H,t)$ on the acquisition surface (a measure space $(S,\mu)$) at a fixed focal point,
--   $$I_{\mathrm{TA}}=\frac{\iint G^+G^-\,dt\,d\mu}{\iint (G^+)^2\,dt\,d\mu},$$
--   and the misfit of a scalar reflectivity $r$ is $\iint (G^--rG^+)^2\,dt\,d\mu$.
--   8. **One-way decomposition (Section II-B, Appendix C).** In the frequency domain, with $\partial_t\mapsto-i\omega$ and no sources, the pressure $P$ and particle velocity $(V_1,V_2,V_3)$ satisfy $\nabla P=i\omega\rho\,v$ and $-(i\omega/\kappa)P+\nabla\cdot v=0$. Here $\rho$ depends on the depth $x_3$ only and $\kappa$ is the bulk modulus. The wave speed is $c=\sqrt{\kappa/\rho}$, and the vertical wavenumber is $k_{x_3}=\sqrt{\omega^2/c^2-|k_H|^2}$ (principal complex root). The matrix of (C-1) in the wavenumber domain is $\begin{pmatrix}0&i\omega\rho\\ i\omega/\kappa+|k_H|^2/(i\omega\rho)&0\end{pmatrix}$. The one-way fields are $P^\pm=\tfrac12P\pm\frac{\omega\rho}{2k_{x_3}}V_3$ and $Q^\pm=\sqrt{k_{x_3}/(\omega\rho)}\,P^\pm$.
--
--   **Formalization Note** The Dirac pulses of Sections III and A are handled through the weak formulation in item 3, so no distribution theory is needed. The annihilator kernel is defined by eqs. (24), (A-6) and (A-7) and the condition $A=0$ on $t=-\tau$. It is not defined by the diagonal relation (25)/(A-8), whose printed sign is inconsistent with (24) and (17). The density in item 8 depends on $x_3$ alone, which (C-1) as printed requires.
-- source:
--   H. A. Oyekan, Marchenko Theory, Algorithms, and Applications: A Review, arXiv:2608.05214v1 (2026), https://arxiv.org/abs/2608.05214, Section II-A/II-B (eqs. 1-2), Section III-B to III-E (eqs. 14-30), Section VIII-B (eq. 58), Appendix A (eqs. A-3, A-6, A-7), Appendix C (eqs. C-1 to C-9)

import Mathlib

/-!
H. A. Oyekan, *Marchenko Theory, Algorithms, and Applications: A Review*, arXiv:2608.05214v1
(2026): the traveltime coordinate, Webster's horn equation, the impedance scaling and the
scattering potential of Section III-B; the impulse response, reflection response and annihilator
kernel of the 1D Schrödinger equation (Sections III-C, III-D and Appendix A), written in the
distributional (weak) sense; the single-interface reflection problem of Section III-E; the
illumination-compensated image of Section VIII-B; and the one-way decomposition of the acoustic
system of Section II-B and Appendix C.
-/

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace Arxiv2608_05214

/-! ### Section III-B: traveltime coordinate, horn equation, Schrödinger equation -/

/-- Section III-B, p. 4: the one-way traveltime coordinate `τ(x) = ∫_0^x dx'/c(x')`. -/
def travelTime (c : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in (0 : ℝ)..x, 1 / c y

/-- Eq. (14), p. 4: the left side `ρ ∂²u/∂t² - ∂/∂x [ρ c² ∂u/∂x]` of the 1D wave equation for the
particle displacement `u(x, t)`, density `ρ(x)` and wave speed `c(x)`, at the point `(x, t)`. -/
def waveEqLHS (ρ c : ℝ → ℝ) (u : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  ρ x * deriv (fun t => deriv (fun t => u x t) t) t
    - deriv (fun x => ρ x * c x ^ 2 * deriv (fun x => u x t) x) x

/-- Eq. (15), p. 4 (Webster's horn equation): the left side `Z ∂²w/∂t² - ∂/∂τ [Z ∂w/∂τ]` for a
field `w(τ, t)` and the impedance `Z(τ) = ρ c` written as a function of traveltime. -/
def hornEqLHS (Z : ℝ → ℝ) (w : ℝ → ℝ → ℝ) (τ t : ℝ) : ℝ :=
  Z τ * deriv (fun t => deriv (fun t => w τ t) t) t
    - deriv (fun τ => Z τ * deriv (fun τ => w τ t) τ) τ

/-- Eq. (18), p. 5: the scattering potential `q(τ) = η''(τ) / η(τ)` of the square root of the
impedance `η = √(ρ c)`. -/
def scatteringPotential (η : ℝ → ℝ) (τ : ℝ) : ℝ := deriv (deriv η) τ / η τ

/-- Eq. (17), p. 5: the left side `∂²ψ/∂t² - ∂²ψ/∂τ² + q(τ) ψ` of the 1D acoustic Schrödinger
equation for a classical field `ψ(τ, t)`. -/
def schrodingerLHS (q : ℝ → ℝ) (ψ : ℝ → ℝ → ℝ) (τ t : ℝ) : ℝ :=
  deriv (fun t => deriv (fun t => ψ τ t) t) t - deriv (fun τ => deriv (fun τ => ψ τ t) τ) τ
    + q τ * ψ τ t

/-! ### Distributional solutions of eq. (17) with a leading `δ(t - τ)` -/

/-- Test functions on the `(τ, t)` plane: smooth with compact support. Points are pairs
`p = (τ, t)`. -/
def IsTestFunction (χ : ℝ × ℝ → ℝ) : Prop := ContDiff ℝ ∞ χ ∧ HasCompactSupport χ

/-- The operator of eq. (17), `∂_t² - ∂_τ² + q(τ)`, applied to a function `χ(τ, t)` of the point
`p = (τ, t)`. It is formally self-adjoint, so it is also the operator of the weak form. -/
def schrodingerOp (q : ℝ → ℝ) (χ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun t => deriv (fun t => χ (p.1, t)) t) p.2
    - deriv (fun τ => deriv (fun τ => χ (τ, p.2)) τ) p.1 + q p.1 * χ p

/-- Eqs. (17), (21), (24): the distribution `ψ = δ(t - τ) + g(τ, t) 1_S(τ, t)` (a unit Dirac pulse
on the line `t = τ` plus a function on the region `S`) solves eq. (17) in the distributional sense
on the open set `U`: `⟨ψ, (∂_t² - ∂_τ² + q) χ⟩ = 0` for every test function `χ` supported in `U`,
where `⟨δ(t - τ), φ⟩ = ∫ φ(τ, τ) dτ`. -/
def IsDeltaFrontSolution (q : ℝ → ℝ) (g : ℝ × ℝ → ℝ) (S U : Set (ℝ × ℝ)) : Prop :=
  ∀ χ : ℝ × ℝ → ℝ, IsTestFunction χ → tsupport χ ⊆ U →
    (∫ τ, schrodingerOp q χ (τ, τ)) + (∫ p in S, g p * schrodingerOp q χ p) = 0

/-- Eqs. (19)-(23) and (A-3), pp. 5-6 and 30: `g` is the tail and `R` the reflection response of
the causal impulse response of eq. (17) to a unit pulse incident from the left. The field
`ψ = δ(t - τ) + g(τ, t) H(t - τ)` solves eq. (17) on the whole plane, `g` is `C²` up to the wave
front `t = τ`, in the free region `τ < 0` the field is the incident pulse plus the reflected wave
`R(t + τ)` (eq. (23)), and `R` is causal, `R(t) = 0` for `t < 0` (Appendix A-C). -/
def IsImpulseResponseTail (q : ℝ → ℝ) (g : ℝ × ℝ → ℝ) (R : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 g {p : ℝ × ℝ | p.1 ≤ p.2} ∧
  IsDeltaFrontSolution q g {p : ℝ × ℝ | p.1 < p.2} Set.univ ∧
  (∀ τ t : ℝ, τ < 0 → τ ≤ t → g (τ, t) = R (t + τ)) ∧
  (∀ s : ℝ, s < 0 → R s = 0)

/-- Eq. (23) and Appendix A-C, pp. 6 and 31: `R` is the reflection response of the scaled field
`ψ`, recorded at `τ = 0`, for a unit impulse incident from the left. -/
def IsReflectionResponse (q : ℝ → ℝ) (R : ℝ → ℝ) : Prop := ∃ g, IsImpulseResponseTail q g R

/-- Eq. (24) and eqs. (A-6)-(A-7), pp. 6 and 30: `A(τ, t)` is the annihilator kernel. The field
`ψ_a = δ(t - τ) + A(τ, t) 1_{|t| < τ}` (the transformation-operator representation (A-6) applied
to the free pulse `ψ₀(s, t) = δ(t - s)`) solves eq. (17) on `τ > 0`, `A` is `C²` on the closed
cone `|t| ≤ τ`, and `A` vanishes on the characteristic `t = -τ`. -/
def IsAnnihilatorKernel (q : ℝ → ℝ) (A : ℝ × ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 A {p : ℝ × ℝ | |p.2| ≤ p.1} ∧
  IsDeltaFrontSolution q A {p : ℝ × ℝ | |p.2| < p.1} {p : ℝ × ℝ | 0 < p.1} ∧
  ∀ τ : ℝ, 0 ≤ τ → A (τ, -τ) = 0

/-! ### Section III-E: a single interface -/

/-- Section III-E, eqs. (29)-(30), p. 7: the scaled field above an interface at traveltime `τ₀`,
an incident wave `f(t - τ)` plus its reflection `r f(t + τ - 2τ₀)`; at `τ = 0` the reflected part is
`r f(t - 2τ₀)`, the response to `f` of `R(t) = r δ(t - 2τ₀)`. -/
def interfaceAbove (f : ℝ → ℝ) (r τ₀ τ t : ℝ) : ℝ := f (t - τ) + r * f (t + τ - 2 * τ₀)

/-- Section III-E, p. 7: the scaled field below the interface, the transmitted wave `T f(t - τ)`. -/
def interfaceBelow (f : ℝ → ℝ) (T τ t : ℝ) : ℝ := T * f (t - τ)

/-- Section III-E, p. 7: continuity at `τ = τ₀` of the displacement `u = ψ / η` and of the traction
`ρ c² ∂u/∂x = η² ∂u/∂τ`, for the scaled fields `ψ = η u` above (`η = η₁`) and below (`η = η₂`)
the interface. -/
def SatisfiesInterfaceConditions (η₁ η₂ τ₀ : ℝ) (f : ℝ → ℝ) (r T : ℝ) : Prop :=
  (∀ t : ℝ, interfaceAbove f r τ₀ τ₀ t / η₁ = interfaceBelow f T τ₀ t / η₂) ∧
  (∀ t : ℝ, η₁ ^ 2 * deriv (fun τ => interfaceAbove f r τ₀ τ t / η₁) τ₀ =
    η₂ ^ 2 * deriv (fun τ => interfaceBelow f T τ t / η₂) τ₀)

/-! ### Section VIII-B: illumination-compensated image -/

section Imaging

variable {S : Type*} [MeasurableSpace S]

/-- Eq. (58), p. 15: the illumination-compensated image at a fixed focal point `x_A`,
`I_TA = ∫∫ G⁺ G⁻ dt dx_H / ∫∫ |G⁺|² dt dx_H`, for real one-way Green's functions
`G^±(x_H, t)` on the acquisition surface `∂D₀` (carrying the measure `μ`) and time. -/
def trueAmplitudeImage (μ : Measure S) (Gp Gm : S → ℝ → ℝ) : ℝ :=
  (∫ p, Gp p.1 p.2 * Gm p.1 p.2 ∂(μ.prod volume)) / ∫ p, Gp p.1 p.2 ^ 2 ∂(μ.prod volume)

/-- Section VIII-B, p. 15: the least-squares misfit `∫∫ |G⁻ - r G⁺|² dt dx_H` of a scalar
reflectivity `r` at the focal point. -/
def scalarReflectivityMisfit (μ : Measure S) (Gp Gm : S → ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ p, (Gm p.1 p.2 - r * Gp p.1 p.2) ^ 2 ∂(μ.prod volume)

end Imaging

/-! ### Section II-B and Appendix C: one-way decomposition -/

/-- Eqs. (1)-(2), p. 3, in the frequency domain with `f = 0` and `q = 0`: with the Fourier
convention of Section II (`∂_t ↦ -iomega`), the pressure `P(x₁, x₂, x₃)` and particle velocity
`(V₁, V₂, V₃)` satisfy `∇P = iomegaρ v` and `(-iomega/κ) P + ∇·v = 0`. The density `ρ` depends on the depth
`x₃` only; the bulk modulus `κ` may depend on all coordinates. -/
def IsFreqAcousticField (omega : ℝ) (ρ : ℝ → ℝ) (κ : ℝ → ℝ → ℝ → ℝ)
    (P V₁ V₂ V₃ : ℝ → ℝ → ℝ → ℂ) : Prop :=
  (∀ x₁ x₂ x₃ : ℝ, deriv (fun s => P s x₂ x₃) x₁ = Complex.I * omega * ρ x₃ * V₁ x₁ x₂ x₃) ∧
  (∀ x₁ x₂ x₃ : ℝ, deriv (fun s => P x₁ s x₃) x₂ = Complex.I * omega * ρ x₃ * V₂ x₁ x₂ x₃) ∧
  (∀ x₁ x₂ x₃ : ℝ, deriv (fun s => P x₁ x₂ s) x₃ = Complex.I * omega * ρ x₃ * V₃ x₁ x₂ x₃) ∧
  (∀ x₁ x₂ x₃ : ℝ, -(Complex.I * omega / κ x₁ x₂ x₃) * P x₁ x₂ x₃
      + deriv (fun s => V₁ s x₂ x₃) x₁ + deriv (fun s => V₂ x₁ s x₃) x₂
      + deriv (fun s => V₃ x₁ x₂ s) x₃ = 0)

/-- Section II-A, p. 3: the wave speed `c = √(κ/ρ)` (`κ = ρ c²`). -/
def soundSpeed (ρ κ : ℝ) : ℝ := Real.sqrt (κ / ρ)

/-- Eq. (C-7), p. 33: the vertical wavenumber `k_{x₃} = √(omega²/c² - |k_H|²)` (principal complex
square root), for horizontal wavenumber `k_H = (k₁, k₂)`. -/
def verticalWavenumber (omega c k₁ k₂ : ℝ) : ℂ :=
  ((omega ^ 2 / c ^ 2 - (k₁ ^ 2 + k₂ ^ 2) : ℝ) : ℂ) ^ (1 / 2 : ℂ)

/-- Eq. (C-1), p. 32, in the horizontal-wavenumber domain of a laterally invariant layer
(`∇_H² ↦ -|k_H|²`): the matrix `[[0, iomegaρ], [iomega/κ - (-|k_H|²)/(iomegaρ), 0]]`. -/
def decompMatrix (omega ρ κ k₁ k₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, Complex.I * omega * ρ;
    Complex.I * omega / κ - (-(k₁ ^ 2 + k₂ ^ 2 : ℝ) : ℂ) / (Complex.I * omega * ρ), 0]

/-- Eq. (C-2), p. 32 (and Section II-B): the pressure-normalised downgoing field
`P⁺ = P/2 + (omegaρ / (2 k_{x₃})) V₃`. -/
def downgoingP (omega ρ : ℝ) (k : ℂ) (P V : ℂ) : ℂ := P / 2 + (omega * ρ : ℂ) / (2 * k) * V

/-- Eq. (C-3), p. 32 (and Section II-B): the pressure-normalised upgoing field
`P⁻ = P/2 - (omegaρ / (2 k_{x₃})) V₃`. -/
def upgoingP (omega ρ : ℝ) (k : ℂ) (P V : ℂ) : ℂ := P / 2 - (omega * ρ : ℂ) / (2 * k) * V

/-- Eq. (C-6), p. 32: the flux-normalised one-way field `Q^± = √(k_{x₃} / (omegaρ)) P^±`. -/
def fluxNormalised (omega ρ : ℝ) (k : ℂ) (Ppm : ℂ) : ℂ := (k / (omega * ρ : ℂ)) ^ (1 / 2 : ℂ) * Ppm

end Arxiv2608_05214


