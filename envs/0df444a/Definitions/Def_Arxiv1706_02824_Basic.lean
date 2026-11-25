-- Prove2me | Definitions.Def_Arxiv1706_02824_Basic
-- name    : Arxiv1706_02824_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T00:40:21.294416+00:00
-- url     : https://prove2.me/theorems/d6dfdfa9-1321-404b-8bf0-7babc86062e5
-- title:
--   Circular Gaussian fields, intensity autocovariances, far-field cross-spectral densities and single-mode coherent states
-- statement:
--   Objects of Sections 2-6 and the Appendix of Gureyev, Kozlov, Paganin, Nesterets, de Hoog and Quiney (2017). One transverse dimension is used throughout, as in the paper.
--
--   1. **Circular Gaussian field.** A family of complex amplitudes $U_i$ on a probability space has circular Gaussian statistics if every finite subfamily is jointly Gaussian (real and imaginary parts), $E[U_i]=0$ and $E[U_iU_j]=0$ for all $i,j$.
--   2. **Exposure-averaged intensity and its autocovariance (eq. 6).** For a field $U(x,t)$, $I_T(x)=T^{-1}\int_{-T/2}^{T/2}|U(x,t)|^2\,dt$ and $C_T(x_1,x_2)=\langle I_T(x_1)I_T(x_2)\rangle-\langle I_T(x_1)\rangle\langle I_T(x_2)\rangle$.
--   3. **Cross-spectral density (Appendix).** $W(x_1,x_2,\cdot)$ is integrable and $\langle U(x_1,t_1)U^*(x_2,t_2)\rangle=\int W(x_1,x_2,\nu)e^{i2\pi\nu(t_1-t_2)}\,d\nu$, which is the meaning of $\langle U(x_1,\nu)U^*(x_2,\nu')\rangle=W(x_1,x_2,\nu)\delta(\nu-\nu')$.
--   4. **Kernels.** For a spectral function $w$, $\mathcal S_T[w]=\iint w(\nu_1)w^*(\nu_2)\,\mathrm{sinc}^2[\pi(\nu_1-\nu_2)T]\,d\nu_1d\nu_2$ with $\mathrm{sinc}\,y=\sin y/y$ (right side of eq. 6). $f_T(\nu)=T\,\mathrm{sinc}^2(\pi\nu T)=\sin^2(\pi\nu T)/(\pi^2\nu^2T)$ with $f_T(0)=T$. The coherence time is $T_c=\int s^2(\nu)\,d\nu$.
--   5. **Source and far field (eqs. 9-10).** $\hat f(u)=\int e^{-i2\pi ux}f(x)\,dx$. The wavelength is $\lambda=c/\nu$. The quasi-homogeneous model is $W_0(x_1',x_2',\nu)=S_0(\tfrac{x_1'+x_2'}2,\nu)\,g_0(x_1'-x_2',\nu)$ with $S_0\ge0$ and $g_0(0,\nu)=1$. The far-field cross-spectral density is $W_R(x_1,x_2,\nu)=\frac{e^{i\psi}}{\lambda R}\hat S_0(\tfrac{x_1-x_2}{\lambda R},\nu)\,\hat g_0(\tfrac{x_1+x_2}{2\lambda R},\nu)$ with $\psi=\pi(x_1^2-x_2^2)/(\lambda R)$.
--   6. **Flat-field noise (Section 4).** $\Gamma[f](x')=\int f(y')f(x'+y')\,dy'$ is the autocorrelation and $(f*g)(r)=\int f(r-y)g(y)\,dy$ the convolution. $\sigma^2(x,\nu)=|\hat S_0(0,\nu)|^2|\hat g_0(x/(\lambda R),\nu)|^2/(\lambda^2R^2)$ and $H(r,\nu)=|\hat S_0(r/(\lambda R),\nu)|^2$. On a stationary patch around $x$, the filtered autocovariance is $r\mapsto T^{-1}\int_{\nu>0}\sigma^2(x,\nu)(H*P_2)(r,\nu)/H(0,\nu)\,d\nu$ with $P_2=\Gamma[P]$, and the noise power spectrum $W_{T,R,x}(\xi)$ is its Fourier transform in $r$.
--   7. **Quasi-monochromatic coherence factors (Section 5).** For amplitudes $V(x)$: $J(x_1,x_2)=\langle V^*(x_1)V(x_2)\rangle$, $\langle I(x)\rangle=\langle|V(x)|^2\rangle$, and $C(x_1,x_2)$ is the covariance of $|V(x_1)|^2$ and $|V(x_2)|^2$. Then $\gamma^{(1,1)}=J/(\langle I_1\rangle^{1/2}\langle I_2\rangle^{1/2})$, $c^{(1,1)}$ is the correlation coefficient of the amplitudes, $c^{(2,2)}=C_{12}/(C_{11}C_{22})^{1/2}$ and $\gamma^{(2,2)}=\langle I_1I_2\rangle/(\langle I_1\rangle\langle I_2\rangle)$.
--   8. **Single-mode coherent state (Section 6).** States are Fock-coefficient sequences $\psi:\mathbb N\to\mathbb C$, with $(a\psi)(n)=\sqrt{n+1}\,\psi(n+1)$ and $(a^\dagger\psi)(n+1)=\sqrt{n+1}\,\psi(n)$. The coherent state is $|\alpha\rangle_n=e^{-|\alpha|^2/2}\alpha^n/\sqrt{n!}$, and $\langle\varphi|\psi\rangle=\sum_n\varphi(n)^*\psi(n)$. The field operators are $E^+(x)=i(\hbar\omega/2)^{1/2}u(x)a$ and $E^-(x)=-i(\hbar\omega/2)^{1/2}u^*(x)a^\dagger$. The intensity operator is $G(x)=E^-(x)E^+(x)$. From these come $C_\alpha(x_1,x_2)=\langle G(x_1)G(x_2)\rangle-\langle G(x_1)\rangle\langle G(x_2)\rangle$, the normally ordered correlation $\langle E^-(x_1)E^-(x_2)E^+(x_1)E^+(x_2)\rangle$, the factors $\gamma_\alpha^{(2,2)}$ of eqs. (30)-(31) and $\mathrm{SNR}^2=\langle G\rangle^2/C_\alpha(x,x)$.
--   9. **Fresnel propagation (eq. 3).** $U_R(x)=\frac{e^{ikR}}{i\sqrt{\lambda R}}\int e^{i\pi(x-x')^2/(\lambda R)}U_0(x')\,dx'$ with $k=2\pi/\lambda$.
--
--   **Formalization Note** Expectations in a coherent state are computed on Fock coefficients, where the series converge absolutely. The noise power spectrum is the forward Fourier transform in $r$, which coincides with the inverse transform the paper mentions because the function is even in $r$.
-- source:
--   Gureyev, Kozlov, Paganin, Nesterets, de Hoog and Quiney, On the van Cittert - Zernike theorem for intensity correlations and its applications, arXiv:1706.02824v1 (2017), Sections 2-6 and Appendix, eqs. (1)-(10), (13)-(16), (19)-(21), (22)-(32), (A1)-(A10)

import Mathlib

/-!
Gureyev, Kozlov, Paganin, Nesterets, de Hoog and Quiney, *On the van Cittert - Zernike theorem for
intensity correlations and its applications*, arXiv:1706.02824v1 (2017): the circular Gaussian
field model, exposure-averaged intensities, cross-spectral densities and intensity autocovariances
of Sections 2-3 and the Appendix; the far-field quasi-homogeneous model of eqs. (9)-(10); the
flat-field noise quantities of Section 4; the coherence factors of Section 5; and the single-mode
coherent-state field operators of Section 6.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ComplexConjugate

noncomputable section

namespace Arxiv1706_02824

section Classical

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Section 2, the assumption before eq. (2): the complex amplitudes `U i` have circular Gaussian
statistics, i.e. every finite family of them is jointly Gaussian (as a vector of real and
imaginary parts), with `E[U i] = 0` and `E[U i U j] = 0` (Goodman, *Statistical Optics*). -/
def IsCircularGaussian {ι : Type*} (P : Measure Omega) (U : ι → Omega → ℂ) : Prop :=
  IsGaussianProcess U P ∧ (∀ i, ∫ w, U i w ∂P = 0) ∧ (∀ i j, ∫ w, U i w * U j w ∂P = 0)

/-- Section 2, before eq. (6): the intensity averaged over one exposure of duration `T`,
`I_{T,R}(x) = T⁻¹ ∫_{-T/2}^{T/2} |U_R(x,t)|² dt`, for a field `U (x, t)`. -/
def timeAvgIntensity (U : ℝ × ℝ → Omega → ℂ) (T x : ℝ) (w : Omega) : ℝ :=
  T⁻¹ * ∫ t in (-T / 2)..(T / 2), ‖U (x, t) w‖ ^ 2

/-- Eq. (6), first line (and eq. (A1)): the intensity autocovariance
`C_{T,R}(x₁,x₂) = ⟨I_{T,R}(x₁) I_{T,R}(x₂)⟩ - ⟨I_{T,R}(x₁)⟩⟨I_{T,R}(x₂)⟩`. -/
def intensityAutocov (P : Measure Omega) (U : ℝ × ℝ → Omega → ℂ) (T x1 x2 : ℝ) : ℝ :=
  (∫ w, timeAvgIntensity U T x1 w * timeAvgIntensity U T x2 w ∂P) -
    (∫ w, timeAvgIntensity U T x1 w ∂P) * (∫ w, timeAvgIntensity U T x2 w ∂P)

/-- Appendix, after eq. (A6): `W(x₁,x₂,ν)` is the cross-spectral density of the field,
`⟨U(x₁,ν) U*(x₂,ν')⟩ = W(x₁,x₂,ν) δ(ν - ν')` with `U(x,t) = ∫ U(x,ν) exp(i2πνt) dν` (eq. (A2));
equivalently `W(x₁,x₂,·)` is integrable and
`⟨U(x₁,t₁) U*(x₂,t₂)⟩ = ∫ W(x₁,x₂,ν) exp(i2πν(t₁ - t₂)) dν`. -/
def IsCrossSpectralDensity (P : Measure Omega) (U : ℝ × ℝ → Omega → ℂ)
    (W : ℝ → ℝ → ℝ → ℂ) : Prop :=
  ∀ x1 x2, Integrable (W x1 x2) ∧ ∀ t1 t2,
    ∫ w, U (x1, t1) w * conj (U (x2, t2) w) ∂P =
      ∫ ν : ℝ, W x1 x2 ν * Complex.exp (2 * π * Complex.I * ((ν * (t1 - t2) : ℝ) : ℂ))

/-- Eq. (6), second line: `∬ W(ν₁) W*(ν₂) sinc²[π(ν₁ - ν₂)T] dν₁ dν₂` for a spectral
function `W = W_R(x₁,x₂,·)`, with `sinc y = sin y / y`. -/
def sincSqIntegral (W : ℝ → ℂ) (T : ℝ) : ℂ :=
  ∫ ν1, ∫ ν2, W ν1 * conj (W ν2) * ((Real.sinc (π * (ν1 - ν2) * T) ^ 2 : ℝ) : ℂ)

/-- Eq. (8'): the coherence time `T_c = ∫ s²(ν) dν` of cross-spectrally pure light with
normalised spectrum `s`. -/
def coherenceTime (s : ℝ → ℝ) : ℝ := ∫ ν, s ν ^ 2

/-- Appendix, before eq. (A10): `f_T(ν) = sin²(πνT)/(π²ν²T)`, so that
`sinc²(πνT) = (1/T) f_T(ν)`; written `T sinc²(πνT)`, which takes the limiting value `T`
at `ν = 0`. -/
def fejerKernelT (T ν : ℝ) : ℝ := T * Real.sinc (π * ν * T) ^ 2

/-- Section 3, after eq. (10): the Fourier transform with respect to the position variable,
`f̂(u) = ∫ exp(-i2πux) f(x) dx`. -/
def ft (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-(2 * π * Complex.I * ((u * x : ℝ) : ℂ))) * f x

/-- Section 2, after eq. (6): the wavelength `λ = c/ν` of temporal frequency `ν`. -/
def wavelength (c ν : ℝ) : ℝ := c / ν

/-- Eq. (9): the quasi-homogeneous model of the source-plane cross-spectral density,
`W₀(x₁',x₂',ν) = S₀((x₁'+x₂')/2, ν) g₀(x₁'-x₂', ν)`, where `S₀ ≥ 0` is the spectral density and
`g₀` the spectral degree of coherence, `g₀(0,ν) = 1`. -/
def IsQuasiHomogeneous (W0 : ℝ → ℝ → ℝ → ℂ) (S0 : ℝ → ℝ → ℝ) (g0 : ℝ → ℝ → ℂ) : Prop :=
  (∀ x ν, 0 ≤ S0 x ν) ∧ (∀ ν, g0 0 ν = 1) ∧
    ∀ x1 x2 ν, W0 x1 x2 ν = (S0 ((x1 + x2) / 2) ν : ℂ) * g0 (x1 - x2) ν

/-- Eq. (10): the far-field cross-spectral density of a quasi-homogeneous source,
`W_R(x₁,x₂,ν) = exp(iψ)/(λR) Ŝ₀((x₁-x₂)/(λR), ν) ĝ₀((x₁+x₂)/(2λR), ν)`,
`ψ = π(x₁² - x₂²)/(λR)`, `λ = c/ν`. -/
def farFieldCSD (c R : ℝ) (S0 : ℝ → ℝ → ℝ) (g0 : ℝ → ℝ → ℂ) (x1 x2 ν : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((π * (x1 ^ 2 - x2 ^ 2) / (wavelength c ν * R) : ℝ) : ℂ)) /
      ((wavelength c ν * R : ℝ) : ℂ) *
    ft (fun y => (S0 y ν : ℂ)) ((x1 - x2) / (wavelength c ν * R)) *
    ft (fun y => g0 y ν) ((x1 + x2) / (2 * wavelength c ν * R))

/-- Section 4, after eq. (16): the autocorrelation `Γ(x') = ∫ f(y') f(x'+y') dy'` (used for
`Γ₀` of the source spectral density, and for `P₂` of the PSF after eq. (15)). -/
def autocorr (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y, f y * f (x + y)

/-- Eq. (15): the convolution `(f * g)(r) = ∫ f(r - y) g(y) dy`. -/
def conv (f g : ℝ → ℝ) (r : ℝ) : ℝ := ∫ y, f (r - y) * g y

/-- Section 4, after eq. (13): the noise variance
`σ²(x,ν) = |Ŝ₀(0,ν)|² |ĝ₀(x/(λR),ν)|² / (λ²R²)`, `λ = c/ν`. -/
def noiseVariance (c R : ℝ) (S0 : ℝ → ℝ → ℝ) (g0 : ℝ → ℝ → ℂ) (x ν : ℝ) : ℝ :=
  ‖ft (fun y => (S0 y ν : ℂ)) 0‖ ^ 2 *
      ‖ft (fun y => g0 y ν) (x / (wavelength c ν * R))‖ ^ 2 /
    (wavelength c ν ^ 2 * R ^ 2)

/-- Section 4, after eq. (13): the noise correlation `H(r,ν) = |Ŝ₀(r/(λR),ν)|²`, `λ = c/ν`. -/
def noiseCorrelation (c R : ℝ) (S0 : ℝ → ℝ → ℝ) (r ν : ℝ) : ℝ :=
  ‖ft (fun y => (S0 y ν : ℂ)) (r / (wavelength c ν * R))‖ ^ 2

/-- Eq. (15), last line, on a "stationary patch" around the mean coordinate `x = (x₁+x₂)/2`:
the autocovariance of the PSF-filtered intensity as a function of `r = x₁ - x₂`,
`T⁻¹ ∫ σ²(x,ν) (H * P₂)(r,ν) / H(0,ν) dν` (frequencies `ν > 0`). -/
def patchAutocov (c R T : ℝ) (S0 : ℝ → ℝ → ℝ) (g0 : ℝ → ℝ → ℂ) (Pf : ℝ → ℝ) (x r : ℝ) : ℝ :=
  T⁻¹ * ∫ ν in Set.Ioi 0,
    noiseVariance c R S0 g0 x ν * conv (fun r' => noiseCorrelation c R S0 r' ν) (autocorr Pf) r /
      noiseCorrelation c R S0 0 ν

/-- Eq. (16), left side: the noise power spectrum `W_{T,R,x}(ξ)`, the Fourier transform of the
patch autocovariance with respect to `r = x₁ - x₂`. -/
def noisePowerSpectrum (c R T : ℝ) (S0 : ℝ → ℝ → ℝ) (g0 : ℝ → ℝ → ℂ) (Pf : ℝ → ℝ)
    (x ξ : ℝ) : ℂ :=
  ft (fun r => (patchAutocov c R T S0 g0 Pf x r : ℂ)) ξ

/-- Eq. (4): the mutual intensity `J_R(x₁,x₂) = ⟨U*(x₁) U(x₂)⟩` of quasi-monochromatic
amplitudes `V x`. -/
def mutualIntensity (P : Measure Omega) (V : ℝ → Omega → ℂ) (x1 x2 : ℝ) : ℂ :=
  ∫ w, conj (V x1 w) * V x2 w ∂P

/-- Eq. (4): the mean intensity `⟨I_R(x)⟩ = ⟨|U(x)|²⟩`. -/
def meanIntensity (P : Measure Omega) (V : ℝ → Omega → ℂ) (x : ℝ) : ℝ :=
  ∫ w, ‖V x w‖ ^ 2 ∂P

/-- Eq. (1): the intensity autocovariance `C_R(x₁,x₂) = ⟨I(x₁)I(x₂)⟩ - ⟨I(x₁)⟩⟨I(x₂)⟩` of
quasi-monochromatic amplitudes, `I(x) = |U(x)|²`. -/
def qmIntensityCov (P : Measure Omega) (V : ℝ → Omega → ℂ) (x1 x2 : ℝ) : ℝ :=
  (∫ w, ‖V x1 w‖ ^ 2 * ‖V x2 w‖ ^ 2 ∂P) - meanIntensity P V x1 * meanIntensity P V x2

/-- Eq. (20): the second-order coherence factor
`γ^{(1,1)}(x₁,x₂) = J_R(x₁,x₂) / (⟨I(x₁)⟩^{1/2} ⟨I(x₂)⟩^{1/2})`. -/
def coherenceFactor11 (P : Measure Omega) (V : ℝ → Omega → ℂ) (x1 x2 : ℝ) : ℂ :=
  mutualIntensity P V x1 x2 /
    ((Real.sqrt (meanIntensity P V x1) : ℂ) * (Real.sqrt (meanIntensity P V x2) : ℂ))

/-- Eq. (20): the correlation coefficient `c^{(1,1)}(x₁,x₂)` of the complex amplitudes,
`⟨(U(x₁) - ⟨U(x₁)⟩)* (U(x₂) - ⟨U(x₂)⟩)⟩` divided by the product of the standard deviations. -/
def ampCorrCoeff (P : Measure Omega) (V : ℝ → Omega → ℂ) (x1 x2 : ℝ) : ℂ :=
  (∫ w, conj (V x1 w - ∫ w', V x1 w' ∂P) * (V x2 w - ∫ w', V x2 w' ∂P) ∂P) /
    ((Real.sqrt (∫ w, ‖V x1 w - ∫ w', V x1 w' ∂P‖ ^ 2 ∂P) : ℂ) *
      (Real.sqrt (∫ w, ‖V x2 w - ∫ w', V x2 w' ∂P‖ ^ 2 ∂P) : ℂ))

/-- Eq. (19): the spatial correlation coefficient of intensities
`c^{(2,2)}(x₁,x₂) = C_R(x₁,x₂) / [C_R(x₁,x₁) C_R(x₂,x₂)]^{1/2}`. -/
def intensityCorrCoeff (P : Measure Omega) (V : ℝ → Omega → ℂ) (x1 x2 : ℝ) : ℝ :=
  qmIntensityCov P V x1 x2 / Real.sqrt (qmIntensityCov P V x1 x1 * qmIntensityCov P V x2 x2)

/-- Eq. (21): the fourth-order coherence factor
`γ^{(2,2)}(x₁,x₂) = ⟨I(x₁)I(x₂)⟩ / (⟨I(x₁)⟩⟨I(x₂)⟩)`. -/
def coherenceFactor22 (P : Measure Omega) (V : ℝ → Omega → ℂ) (x1 x2 : ℝ) : ℝ :=
  (∫ w, ‖V x1 w‖ ^ 2 * ‖V x2 w‖ ^ 2 ∂P) / (meanIntensity P V x1 * meanIntensity P V x2)

end Classical

section Quantum

/-- Section 6: the annihilation operator `a` of the single mode, acting on Fock-basis
coefficients, `(aψ)(n) = √(n+1) ψ(n+1)`. -/
def annihilation (ψ : ℕ → ℂ) : ℕ → ℂ := fun n => (Real.sqrt (n + 1) : ℂ) * ψ (n + 1)

/-- Section 6: the creation operator `a†` of the single mode, acting on Fock-basis
coefficients, `(a†ψ)(0) = 0`, `(a†ψ)(n+1) = √(n+1) ψ(n)`. -/
def creation (ψ : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => (Real.sqrt (n + 1) : ℂ) * ψ n

/-- Section 6: the Glauber coherent state `|α⟩`, with Fock coefficients
`exp(-|α|²/2) αⁿ / √(n!)`. -/
def coherentState (α : ℂ) : ℕ → ℂ := fun n =>
  (Real.exp (-(‖α‖ ^ 2) / 2) : ℂ) * α ^ n / (Real.sqrt (n.factorial) : ℂ)

/-- The inner product `⟨φ|ψ⟩ = Σₙ φ(n)* ψ(n)` of Fock-basis coefficient sequences. -/
def fockInner (φ ψ : ℕ → ℂ) : ℂ := ∑' n, conj (φ n) * ψ n

/-- Section 6: `E⁺(x) = i (ħω/2)^{1/2} u(x) a`, the positive-frequency field operator of the
single mode with mode function `u`. -/
def fieldPos (hbar ω : ℝ) (u : ℝ → ℂ) (x : ℝ) (ψ : ℕ → ℂ) : ℕ → ℂ := fun n =>
  Complex.I * (Real.sqrt (hbar * ω / 2) : ℂ) * u x * annihilation ψ n

/-- Section 6: `E⁻(x) = (E⁺)†(x) = -i (ħω/2)^{1/2} u*(x) a†`. -/
def fieldNeg (hbar ω : ℝ) (u : ℝ → ℂ) (x : ℝ) (ψ : ℕ → ℂ) : ℕ → ℂ := fun n =>
  -Complex.I * (Real.sqrt (hbar * ω / 2) : ℂ) * conj (u x) * creation ψ n

/-- Section 6, after eq. (23): the intensity operator `G(x) = E⁻(x) E⁺(x)`. -/
def intensityOp (hbar ω : ℝ) (u : ℝ → ℂ) (x : ℝ) (ψ : ℕ → ℂ) : ℕ → ℂ :=
  fieldNeg hbar ω u x (fieldPos hbar ω u x ψ)

/-- Section 6: the expectation value `⟨α|A|α⟩` in the coherent state `|α⟩`. -/
def cohExpect (α : ℂ) (A : (ℕ → ℂ) → ℕ → ℂ) : ℂ :=
  fockInner (coherentState α) (A (coherentState α))

/-- Eq. (25): `C_α(x₁,x₂) = ⟨α|G(x₁)G(x₂)|α⟩ - ⟨α|G(x₁)|α⟩⟨α|G(x₂)|α⟩`; eq. (26):
`V_α(x) = C_α(x,x)`. -/
def cohIntensityAutocov (hbar ω : ℝ) (u : ℝ → ℂ) (α : ℂ) (x1 x2 : ℝ) : ℂ :=
  cohExpect α (fun ψ => intensityOp hbar ω u x1 (intensityOp hbar ω u x2 ψ)) -
    cohExpect α (intensityOp hbar ω u x1) * cohExpect α (intensityOp hbar ω u x2)

/-- Eq. (30), numerator: the normally ordered correlation
`⟨α|E⁻(x₁)E⁻(x₂)E⁺(x₁)E⁺(x₂)|α⟩`. -/
def normalOrderedCorr (hbar ω : ℝ) (u : ℝ → ℂ) (α : ℂ) (x1 x2 : ℝ) : ℂ :=
  cohExpect α (fun ψ => fieldNeg hbar ω u x1 (fieldNeg hbar ω u x2
    (fieldPos hbar ω u x1 (fieldPos hbar ω u x2 ψ))))

/-- Eq. (30): the normally ordered fourth-order coherence factor
`⟨α|E⁻(x₁)E⁻(x₂)E⁺(x₁)E⁺(x₂)|α⟩ / (⟨α|E⁻(x₁)E⁺(x₁)|α⟩⟨α|E⁻(x₂)E⁺(x₂)|α⟩)`. -/
def cohGamma22Normal (hbar ω : ℝ) (u : ℝ → ℂ) (α : ℂ) (x1 x2 : ℝ) : ℂ :=
  normalOrderedCorr hbar ω u α x1 x2 /
    (cohExpect α (intensityOp hbar ω u x1) * cohExpect α (intensityOp hbar ω u x2))

/-- Eq. (31): `γ_α^{(2,2)}(x₁,x₂) = ⟨α|G(x₁)G(x₂)|α⟩ / (I_α(x₁) I_α(x₂))` with
`I_α(x) = ⟨α|G(x)|α⟩`. -/
def cohGamma22 (hbar ω : ℝ) (u : ℝ → ℂ) (α : ℂ) (x1 x2 : ℝ) : ℂ :=
  cohExpect α (fun ψ => intensityOp hbar ω u x1 (intensityOp hbar ω u x2 ψ)) /
    (cohExpect α (intensityOp hbar ω u x1) * cohExpect α (intensityOp hbar ω u x2))

/-- Eq. (32): the squared signal-to-noise ratio `SNR²(x) = I_α(x)² / V_α(x)`. -/
def snrSq (hbar ω : ℝ) (u : ℝ → ℂ) (α : ℂ) (x : ℝ) : ℂ :=
  cohExpect α (intensityOp hbar ω u x) ^ 2 / cohIntensityAutocov hbar ω u α x x

end Quantum

/-- Eq. (3): Fresnel propagation over distance `R` at wavelength `λ`,
`U_R(x) = exp(ikR)/(i√(λR)) ∫ exp(iπ(x - x')²/(λR)) U₀(x') dx'`, `k = 2π/λ`. -/
def fresnelProp (lam R : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((2 * π / lam * R : ℝ) : ℂ)) /
      (Complex.I * (Real.sqrt (lam * R) : ℂ)) *
    ∫ x', Complex.exp (Complex.I * ((π / (lam * R) * (x - x') ^ 2 : ℝ) : ℂ)) * f x'

end Arxiv1706_02824


