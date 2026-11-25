-- Prove2me | Definitions.Def_Arxiv2201_05558_Basic
-- name    : Arxiv2201_05558_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T10:48:04.602008+00:00
-- url     : https://prove2.me/theorems/6cd53df6-28b6-42f3-9266-7f767a236429
-- title:
--   Time-reversal mirror, transport equation and explicit moment coefficients (Garnier–Sølna)
-- statement:
--   Objects of Sections 3.1, 5.4, 5.6 and 5.7 of Garnier and Sølna (2022). Throughout, $\mathbb{R}^2$ is the transverse plane with Euclidean norm $|\cdot|$, inner product $x\cdot\zeta$ and Lebesgue measure.
--
--   1. **Time-reversal mirror (Section 3.1).** For a field $G:\mathbb{R}^2\to\mathbb{C}$ on the mirror plane (a Green's function $x'\mapsto\mathcal G(\omega,L,\cdot,x')$), a Gaussian element of radius $\rho_0$ centred at $x_m$ gives $(2\pi\rho_0^2)^{-1}\int G(x_m+x')e^{-|x'|^2/(2\rho_0^2)}dx'$ (eqs. (3.1), (3.3)). The time-reversed field of a Gaussian mirror of radius $R_m$ is $\hat u_{\rm tr}=\int \hat u_{\rm em}(x_m)e^{-|x_m|^2/R_m^2}\overline{\hat u_{\rm rec}(x_m)}dx_m$ (eq. (3.2)), and $K_0=c_o^2(r_0^2-\rho_0^2)/(16\pi\omega\tilde\omega\rho_0^2r_0^2)$ (eq. (3.5)).
--   2. **Transport equation (Section 5.4).** $\hat C(k)=\int C(x)e^{-ik\cdot x}dx$ is the Fourier transform of the covariance function $C$, and $K(z)=(2\pi)^4\exp(-\omega_0^2C(0)z/(4c_o^2))$ (eq. (5.13)). The right-hand side of (5.14) is
--   $$\frac{ic_o\Omega}{\omega_0^2}|\xi|^2A+\frac{\omega_0^2}{4(2\pi)^2c_o^2}\int\hat C(k)\big[A(\xi-k)e^{\frac{ic_oz}{\omega_0}k\cdot\zeta}-A(\xi)\big]dk+\frac{\omega_0^2}{4(2\pi)^2c_o^2}K(z)\hat C(\xi)e^{\frac{ic_oz}{\omega_0}\xi\cdot\zeta}.$$
--   The function of eq. (5.27) is $A(z,\xi,\zeta,0)=\frac{K(z)}{(2\pi)^2}\int\big[\exp\big(\frac{\omega_0^2}{4c_o^2}\int_0^zC(x+\frac{c_o\zeta}{\omega_0}z')dz'\big)-1\big]e^{-i\xi\cdot x}dx$.
--   3. **The functions $\Psi$ (eqs. (5.43)-(5.46), (5.57)-(5.60)).** With $w=e^{-i\pi/4}$ and a parameter $T\in\mathbb{C}$ ($T=0$ in Proposition 5.4, $T=T_0$ in Proposition 5.7):
--   $$\Psi_a(s)=\ln[\cosh(ws)+T\sinh(ws)],\qquad \Psi_b(s)=\frac{T+\tanh(ws)}{ws\,[1+T\tanh(ws)]},$$
--   $$\Psi_c(s)=\frac{2i\,N(s)}{s^2},\qquad \Psi_d(s)=1-\frac{3i}{s^3}\int_0^sN(s')^2ds',\qquad N(s)=ws\frac{T+\tanh(ws)}{1+T\tanh(ws)}-1+[\cosh(ws)+T\sinh(ws)]^{-1}.$$
--   Here $T_0=2e^{-i\pi/4}\sqrt{c_o^3\Omega/D}/(\omega_0^2\rho_0^2)$ (eq. (5.61)).
--   4. **Coefficients (eqs. (5.39)-(5.42)).** For $\Omega\ge0$ and $s=\sqrt{D\Omega/(4c_o)}\,z$: $a_\Omega(z)=\Psi_a(s)$, $b_\Omega(z)=\frac{\omega_0^2Dz}{16c_o^2}\Psi_b(s)$, $c_\Omega(z)=\frac{\omega_0Dz^2}{16c_o}\Psi_c(s)$ and $d_\Omega(z)=\frac{Dz^3}{48}\Psi_d(s)$. For $\Omega<0$, $(a,b,c,d)_\Omega=\overline{(a,b,c,d)_{-\Omega}}$, as in the proof of Proposition 5.4. The function $\hat A_s(z,x,\zeta,\Omega)=(2\pi)^2\exp[-a_\Omega(z)-b_\Omega(z)|x|^2-c_\Omega(z)x\cdot\zeta-d_\Omega(z)|\zeta|^2]$ is eq. (5.38).
--   5. **Equations of the proofs.** The reduced moment equation of the proof of Proposition 5.4 is
--   $$\partial_z\hat A=-\frac{ic_o\Omega}{\omega_0^2}\Delta_x\hat A-\frac{\omega_0^2D}{16c_o^2}\Big[|x|^2+\frac{z^2c_o^2}{\omega_0^2}|\zeta|^2+\frac{2zc_o}{\omega_0}\zeta\cdot x\Big]\hat A$$
--   on $z>0$, with initial value $\hat A(z,x)\to\hat A_0(x)$ as $z\to0^+$. The coefficient system (5.47)-(5.50) on $z>0$ is
--   $$a'=-i\tfrac{4c_o\Omega}{\omega_0^2}b,\quad b'=\tfrac{\omega_0^2D}{16c_o^2}+i\tfrac{4c_o\Omega}{\omega_0^2}b^2,\quad c'=\tfrac{\omega_0Dz}{8c_o}+i\tfrac{4c_o\Omega}{\omega_0^2}bc,\quad d'=\tfrac{Dz^2}{16}+i\tfrac{c_o\Omega}{\omega_0^2}c^2.$$
--
--   **Formalization Note** The paper does not specify the branch of $\ln$ in $\Psi_a$. Here $\Psi_a$ is the determination continuous in $s\ge0$ with $\Psi_a(0)=0$, written as $\int_0^s w\,\frac{\sinh(wt)+T\cosh(wt)}{\cosh(wt)+T\sinh(wt)}\,dt$. This is the coefficient $a_\Omega$ that solves (5.47) with $a_\Omega(0)=0$. The principal logarithm would jump at $s=\sqrt2\,\pi$, where $\cosh(ws)=-\cosh\pi<0$. The formulas for $\Psi_{b,c,d}$ are undefined at $s=0$; Lean assigns them junk values there, which no statement uses.
-- source:
--   Garnier and Sølna, Speckle Memory Effect in the Frequency Domain and Stability in Time-Reversal Experiments, arXiv:2201.05558v1 (2022), Section 3.1 (eqs. (3.1)-(3.5)), Section 5.4 (eqs. (5.13)-(5.14)), Section 5.6 (eqs. (5.27), (5.38)-(5.50), proof of Proposition 5.4), Section 5.7 (eqs. (5.57)-(5.61))

import Mathlib

/-!
J. Garnier and K. Sølna, *Speckle Memory Effect in the Frequency Domain and Stability in
Time-Reversal Experiments*, arXiv:2201.05558v1 (2022): the time-reversal mirror of Section 3.1,
the transport equation (5.13)-(5.14) of Section 5.4 and its zero-offset solution (5.27), the
explicit coefficient functions of Propositions 5.4 and 5.7 (Sections 5.6 and 5.7), and the
reduced moment equation and coefficient ODE system (5.47)-(5.50) used in their proofs.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace Arxiv2201_05558

/-- The transverse plane `ℝ²` of the paper (Section 2), with its Euclidean norm, inner product
and Lebesgue measure. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-! ### Section 3.1: the time-harmonic time-reversal mirror -/

/-- Eqs. (3.1) and (3.3): the field `G` (a Green's function `x' ↦ 𝒢(ω, L, ·, x')` on the mirror
plane) smoothed by a Gaussian mirror element of radius `ρ₀` centred at `x_m`:
`(2πρ₀²)⁻¹ ∫ G(x_m + x') exp(-|x'|²/(2ρ₀²)) dx'`. -/
def elemField (ρ0 : ℝ) (G : Plane → ℂ) (xm : Plane) : ℂ :=
  (1 / (2 * Real.pi * ρ0 ^ 2) : ℂ) *
    ∫ x', G (xm + x') * (Real.exp (-‖x'‖ ^ 2 / (2 * ρ0 ^ 2)) : ℂ)

/-- Eq. (3.2): the time-reversed field `û_tr = ∫ û_em(x_m) exp(-|x_m|²/R_m²) conj(û_rec(x_m)) dx_m`
for a Gaussian mirror of radius `R_m`, where `û_em` is the element field (3.3) of the emitting
Green's function `G1` and `û_rec` the element field (3.1) of the recording Green's function `G2`. -/
def trField (Rm ρ0 : ℝ) (G1 G2 : Plane → ℂ) : ℂ :=
  ∫ xm, elemField ρ0 G1 xm * (Real.exp (-‖xm‖ ^ 2 / Rm ^ 2) : ℂ) *
    starRingEnd ℂ (elemField ρ0 G2 xm)

/-- Eq. (3.5): the constant `K₀ = c_o²(r₀² - ρ₀²) / (16 π ω ω̃ ρ₀² r₀²)`. -/
def K0 (c0 ω ωt r0 ρ0 : ℝ) : ℝ :=
  c0 ^ 2 * (r0 ^ 2 - ρ0 ^ 2) / (16 * Real.pi * ω * ωt * ρ0 ^ 2 * r0 ^ 2)

/-! ### Section 5.4: the transport equation -/

/-- The Fourier transform `Ĉ(k) = ∫ C(x) e^{-i k·x} dx` of the covariance function `C` of (2.8)
(Section 5.4; `C` is even, so the sign convention of the exponent does not matter). -/
def covFT (C : Plane → ℝ) (k : Plane) : ℂ :=
  ∫ x, (C x : ℂ) * Complex.exp (-(Complex.I * (inner ℝ k x : ℝ)))

/-- Eq. (5.13): `K(z) = (2π)⁴ exp(-ω₀² C(0) z / (4 c_o²))`. -/
def Kcoh (ω0 c0 : ℝ) (C : Plane → ℝ) (z : ℝ) : ℝ :=
  (2 * Real.pi) ^ 4 * Real.exp (-(ω0 ^ 2 / (4 * c0 ^ 2)) * C 0 * z)

/-- Eq. (5.14): the right-hand side of the transport equation for `A(z, ξ, ζ, Ω)` (with `ζ` and
`Ω` frozen):
`(i c_o Ω/ω₀²)|ξ|² A + ω₀²/(4(2π)²c_o²) ∫ Ĉ(k)[A(ξ-k) e^{i c_o z k·ζ/ω₀} - A(ξ)] dk
 + ω₀²/(4(2π)²c_o²) K(z) Ĉ(ξ) e^{i c_o z ξ·ζ/ω₀}`. -/
def transportRHS (ω0 c0 : ℝ) (C : Plane → ℝ) (Ω : ℝ) (ζ : Plane) (A : ℝ → Plane → ℂ)
    (z : ℝ) (ξ : Plane) : ℂ :=
  Complex.I * (c0 * Ω / ω0 ^ 2 * ‖ξ‖ ^ 2 : ℝ) * A z ξ +
    (ω0 ^ 2 / (4 * (2 * Real.pi) ^ 2 * c0 ^ 2) : ℝ) *
      ∫ k, covFT C k * (A z (ξ - k) *
        Complex.exp (Complex.I * (c0 * z / ω0 * inner ℝ k ζ : ℝ)) - A z ξ) +
    (ω0 ^ 2 / (4 * (2 * Real.pi) ^ 2 * c0 ^ 2) : ℝ) * (Kcoh ω0 c0 C z : ℂ) * covFT C ξ *
      Complex.exp (Complex.I * (c0 * z / ω0 * inner ℝ ξ ζ : ℝ))

/-- Eq. (5.27): the explicit function
`A(z, ξ, ζ, 0) = K(z)/(2π)² ∫ [exp(ω₀²/(4c_o²) ∫₀^z C(x + c_o ζ z'/ω₀) dz') - 1] e^{-i ξ·x} dx`. -/
def transportZero (ω0 c0 : ℝ) (C : Plane → ℝ) (ζ : Plane) (z : ℝ) (ξ : Plane) : ℂ :=
  (Kcoh ω0 c0 C z / (2 * Real.pi) ^ 2 : ℝ) *
    ∫ x, ((Real.exp (ω0 ^ 2 / (4 * c0 ^ 2) *
        ∫ z' in (0 : ℝ)..z, C (x + (c0 * z' / ω0) • ζ)) - 1 : ℝ) : ℂ) *
      Complex.exp (-(Complex.I * (inner ℝ ξ x : ℝ)))

/-! ### Sections 5.6-5.7: the functions `Ψ_{a,b,c,d}` -/

/-- The complex number `e^{-iπ/4}`, which appears in (5.43)-(5.46) and (5.57)-(5.61). -/
def eMinusQuarter : ℂ := Complex.exp (-(((Real.pi / 4 : ℝ) : ℂ) * Complex.I))

/-- Eq. (5.57) (eq. (5.43) when `T = 0`): `Ψ_a(s) = ln[cosh(e^{-iπ/4}s) + T sinh(e^{-iπ/4}s)]`,
the logarithm being the determination continuous in `s ≥ 0` with `Ψ_a(0) = 0` (the paper's
`a_Ω` solves (5.47) with `a_Ω(0) = 0`), written as the integral of its `s`-derivative. -/
def psiA (T : ℂ) (s : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..s, eMinusQuarter *
    ((Complex.sinh (eMinusQuarter * t) + T * Complex.cosh (eMinusQuarter * t)) /
      (Complex.cosh (eMinusQuarter * t) + T * Complex.sinh (eMinusQuarter * t)))

/-- Eq. (5.58) (eq. (5.44) when `T = 0`):
`Ψ_b(s) = (T + tanh(e^{-iπ/4}s)) / (e^{-iπ/4}s [1 + T tanh(e^{-iπ/4}s)])`. -/
def psiB (T : ℂ) (s : ℝ) : ℂ :=
  (T + Complex.tanh (eMinusQuarter * s)) /
    (eMinusQuarter * s * (1 + T * Complex.tanh (eMinusQuarter * s)))

/-- The numerator of (5.59) (of (5.45) when `T = 0`), also the integrand base of (5.60):
`e^{-iπ/4}s (T + tanh(e^{-iπ/4}s))/(1 + T tanh(e^{-iπ/4}s)) - 1
 + [cosh(e^{-iπ/4}s) + T sinh(e^{-iπ/4}s)]⁻¹`. -/
def psiNum (T : ℂ) (s : ℝ) : ℂ :=
  eMinusQuarter * s * ((T + Complex.tanh (eMinusQuarter * s)) /
      (1 + T * Complex.tanh (eMinusQuarter * s))) - 1 +
    (Complex.cosh (eMinusQuarter * s) + T * Complex.sinh (eMinusQuarter * s))⁻¹

/-- Eq. (5.59) (eq. (5.45) when `T = 0`): `Ψ_c(s) = 2i · psiNum(s) / s²`. -/
def psiC (T : ℂ) (s : ℝ) : ℂ :=
  2 * Complex.I * psiNum T s / (s : ℂ) ^ 2

/-- Eq. (5.60) (eq. (5.46) when `T = 0`): `Ψ_d(s) = 1 - (3i/s³) ∫₀^s psiNum(s')² ds'`. -/
def psiD (T : ℂ) (s : ℝ) : ℂ :=
  1 - 3 * Complex.I / (s : ℂ) ^ 3 * ∫ t in (0 : ℝ)..s, psiNum T t ^ 2

/-- Eq. (5.61): `T₀ = 2 e^{-iπ/4} √(c_o³ Ω / D) / (ω₀² ρ₀²)` (for `Ω ≥ 0`). -/
def T0 (ω0 c0 D ρ0 Ω : ℝ) : ℂ :=
  2 * eMinusQuarter / (ω0 ^ 2 * ρ0 ^ 2 : ℝ) * (Real.sqrt (c0 ^ 3 * Ω / D) : ℂ)

/-- The argument `s = √(DΩ/(4c_o)) z` of the `Ψ`-functions in (5.39)-(5.42) (for `Ω ≥ 0`). -/
def sArg (c0 D Ω z : ℝ) : ℝ := Real.sqrt (D * Ω / (4 * c0)) * z

/-! ### The coefficients `a_Ω, b_Ω, c_Ω, d_Ω` -/

/-- Eqs. (5.39)-(5.42) for `Ω ≥ 0`: the coefficient `a_Ω(z) = Ψ_a(s)`, the `Ψ`-functions having
parameter `T` (`T = 0` in Proposition 5.4, `T = T₀` in Proposition 5.7). -/
def aPos (c0 D : ℝ) (T : ℂ) (Ω z : ℝ) : ℂ := psiA T (sArg c0 D Ω z)

/-- Eq. (5.40) for `Ω ≥ 0`: `b_Ω(z) = (ω₀² D z / (16 c_o²)) Ψ_b(s)`. -/
def bPos (ω0 c0 D : ℝ) (T : ℂ) (Ω z : ℝ) : ℂ :=
  (ω0 ^ 2 * D * z / (16 * c0 ^ 2) : ℝ) * psiB T (sArg c0 D Ω z)

/-- Eq. (5.41) for `Ω ≥ 0`: `c_Ω(z) = (ω₀ D z² / (16 c_o)) Ψ_c(s)`. -/
def cPos (ω0 c0 D : ℝ) (T : ℂ) (Ω z : ℝ) : ℂ :=
  (ω0 * D * z ^ 2 / (16 * c0) : ℝ) * psiC T (sArg c0 D Ω z)

/-- Eq. (5.42) for `Ω ≥ 0`: `d_Ω(z) = (D z³ / 48) Ψ_d(s)`. -/
def dPos (c0 D : ℝ) (T : ℂ) (Ω z : ℝ) : ℂ :=
  (D * z ^ 3 / 48 : ℝ) * psiD T (sArg c0 D Ω z)

/-- `a_Ω(z)` for every real `Ω`: (5.39) for `Ω ≥ 0`, and `a_Ω = conj(a_{-Ω})` for `Ω < 0` (proof of
Proposition 5.4, p. 21). `T Ω` is the parameter of the `Ψ`-functions at offset `Ω ≥ 0`. -/
def aOm (c0 D : ℝ) (T : ℝ → ℂ) (Ω z : ℝ) : ℂ :=
  if 0 ≤ Ω then aPos c0 D (T Ω) Ω z else starRingEnd ℂ (aPos c0 D (T (-Ω)) (-Ω) z)

/-- `b_Ω(z)` for every real `Ω`: (5.40) for `Ω ≥ 0`, `b_Ω = conj(b_{-Ω})` for `Ω < 0`. -/
def bOm (ω0 c0 D : ℝ) (T : ℝ → ℂ) (Ω z : ℝ) : ℂ :=
  if 0 ≤ Ω then bPos ω0 c0 D (T Ω) Ω z else starRingEnd ℂ (bPos ω0 c0 D (T (-Ω)) (-Ω) z)

/-- `c_Ω(z)` for every real `Ω`: (5.41) for `Ω ≥ 0`, `c_Ω = conj(c_{-Ω})` for `Ω < 0`. -/
def cOm (ω0 c0 D : ℝ) (T : ℝ → ℂ) (Ω z : ℝ) : ℂ :=
  if 0 ≤ Ω then cPos ω0 c0 D (T Ω) Ω z else starRingEnd ℂ (cPos ω0 c0 D (T (-Ω)) (-Ω) z)

/-- `d_Ω(z)` for every real `Ω`: (5.42) for `Ω ≥ 0`, `d_Ω = conj(d_{-Ω})` for `Ω < 0`. -/
def dOm (c0 D : ℝ) (T : ℝ → ℂ) (Ω z : ℝ) : ℂ :=
  if 0 ≤ Ω then dPos c0 D (T Ω) Ω z else starRingEnd ℂ (dPos c0 D (T (-Ω)) (-Ω) z)

/-- Eq. (5.38): the complex Gaussian
`(2π)² exp[-a - b|x|² - c x·ζ - d|ζ|²]`. -/
def gaussForm (a b c d : ℂ) (x ζ : Plane) : ℂ :=
  (2 * Real.pi : ℂ) ^ 2 *
    Complex.exp (-a - b * (‖x‖ ^ 2 : ℝ) - c * (inner ℝ x ζ : ℝ) - d * (‖ζ‖ ^ 2 : ℝ))

/-- Eq. (5.38) with the coefficients (5.39)-(5.42): the function
`Â_s(z, x, ζ, Ω) = (2π)² exp[-a_Ω(z) - b_Ω(z)|x|² - c_Ω(z) x·ζ - d_Ω(z)|ζ|²]`, the `Ψ`-functions
having parameter `T Ω`. -/
def hatAs (ω0 c0 D : ℝ) (T : ℝ → ℂ) (Ω : ℝ) (ζ : Plane) (z : ℝ) (x : Plane) : ℂ :=
  gaussForm (aOm c0 D T Ω z) (bOm ω0 c0 D T Ω z) (cOm ω0 c0 D T Ω z) (dOm c0 D T Ω z) x ζ

/-! ### The equations used in the proofs of Propositions 5.4 and 5.7 -/

/-- Proof of Proposition 5.4 (p. 21): the right-hand side of the equation for `Â_s`,
`-(i c_o Ω/ω₀²) Δ_x Â - (ω₀² D/(16 c_o²)) [|x|² + z² c_o² |ζ|²/ω₀² + 2 z c_o ζ·x/ω₀] Â`. -/
def momentRHS (ω0 c0 D Ω : ℝ) (ζ : Plane) (F : ℝ → Plane → ℂ) (z : ℝ) (x : Plane) : ℂ :=
  -(Complex.I * (c0 * Ω / ω0 ^ 2 : ℝ)) * Laplacian.laplacian (F z) x -
    (ω0 ^ 2 * D / (16 * c0 ^ 2) *
      (‖x‖ ^ 2 + z ^ 2 * c0 ^ 2 / ω0 ^ 2 * ‖ζ‖ ^ 2 + 2 * z * c0 / ω0 * inner ℝ ζ x) : ℝ) * F z x

/-- Proof of Proposition 5.4 (p. 21): `F` solves the equation for `Â_s` on `z > 0`, with
`F(z, x) → F₀(x)` as `z → 0⁺` for every `x` (the initial condition). -/
def SolvesMomentEq (ω0 c0 D Ω : ℝ) (ζ : Plane) (F : ℝ → Plane → ℂ) (F0 : Plane → ℂ) : Prop :=
  (∀ x, Tendsto (fun z => F z x) (𝓝[>] 0) (𝓝 (F0 x))) ∧
    ∀ z : ℝ, 0 < z → ∀ x, HasDerivAt (fun z' => F z' x) (momentRHS ω0 c0 D Ω ζ F z x) z

/-- Eqs. (5.47)-(5.50): on `z > 0`,
`a' = -i(4c_oΩ/ω₀²) b`, `b' = ω₀²D/(16c_o²) + i(4c_oΩ/ω₀²) b²`,
`c' = ω₀Dz/(8c_o) + i(4c_oΩ/ω₀²) b c`, `d' = Dz²/16 + i(c_oΩ/ω₀²) c²`. -/
def SolvesCoefODE (ω0 c0 D Ω : ℝ) (a b c d : ℝ → ℂ) : Prop :=
  ∀ z : ℝ, 0 < z →
    HasDerivAt a (-(Complex.I * (4 * c0 * Ω / ω0 ^ 2 : ℝ)) * b z) z ∧
    HasDerivAt b ((ω0 ^ 2 * D / (16 * c0 ^ 2) : ℝ) +
      Complex.I * (4 * c0 * Ω / ω0 ^ 2 : ℝ) * b z ^ 2) z ∧
    HasDerivAt c ((ω0 * D * z / (8 * c0) : ℝ) +
      Complex.I * (4 * c0 * Ω / ω0 ^ 2 : ℝ) * b z * c z) z ∧
    HasDerivAt d ((D * z ^ 2 / 16 : ℝ) + Complex.I * (c0 * Ω / ω0 ^ 2 : ℝ) * c z ^ 2) z

end Arxiv2201_05558


