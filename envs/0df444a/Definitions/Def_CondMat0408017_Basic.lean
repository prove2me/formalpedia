-- Prove2me | Definitions.Def_CondMat0408017_Basic
-- name    : CondMat0408017_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T19:21:53.593632+00:00
-- url     : https://prove2.me/theorems/f6e16788-d439-5088-b8b0-65df226c3c8a
-- title:
--   Primary fields, planar surface plasmon polaritons, Rayleigh-equation matrix elements, specular kernels and speckle correlation functions for one-dimensional rough surfaces
-- statement:
--   Objects used in the derivations of Sections II-IV of Simonsen (2004), a review of wave scattering from one-dimensional rough surfaces $x_3=\zeta(x_1)$ with harmonic time dependence $e^{-i\omega t}$.
--
--   1. **Primary field and boundary conditions (Sec. II.C).** For $p$ polarization the primary field is $\Phi_p=H_2$, and $E=(-\frac{i}{\omega\varepsilon}\partial_3\Phi,0,\frac{i}{\omega\varepsilon}\partial_1\Phi)$, $H=(0,\Phi,0)$. For $s$ polarization $\Phi_s=E_2$, $E=(0,\Phi,0)$, $H=(\frac{i}{\omega\mu}\partial_3\Phi,0,-\frac{i}{\omega\mu}\partial_1\Phi)$. Write $\kappa=\varepsilon$ for $p$ and $\kappa=\mu$ for $s$. The unit normal into medium $+$ is $n=(-\zeta',0,1)/\sqrt{1+\zeta'^2}$, and $\partial_n=(-\zeta'\partial_1+\partial_3)/\sqrt{1+\zeta'^2}$.
--   2. **Planar SPPs (Sec. II.D).** For real dielectric constants $\varepsilon_\pm$ the decay constants are $\beta_\pm=\sqrt{k^2-\varepsilon_\pm\omega^2/c^2}$. The localized fields are $\Phi^+=A^+e^{-\beta_+x_3}e^{ikx_1}$ ($x_3>0$) and $\Phi^-=A^-e^{\beta_-x_3}e^{ikx_1}$ ($x_3<0$). The flat-interface boundary conditions are $\Phi^+=\Phi^-$ and $\frac1{\kappa^+}\partial_3\Phi^+=\frac1{\kappa^-}\partial_3\Phi^-$ at $x_3=0$ for every $x_1$. A $p$-polarized SPP at $(k,\omega)$ exists if $\beta_\pm$ are real and positive and these conditions with $\kappa^\pm=\varepsilon_\pm$ have a non-zero solution. The free-electron dielectric function is $\varepsilon(\omega)=\varepsilon_\infty(1-\omega_p^2/\omega^2)$, and $\omega_{sp}(k)$ is the expression (21).
--   3. **Rms height difference (Sec. II.G).** For a random profile $\zeta(x_1,\cdot)$ on a probability space, $\sigma(\Delta x_1)=\langle(\zeta(\Delta x_1)-\zeta(0))^2\rangle^{1/2}$.
--   4. **Mean DRC and S-matrix (Sec. III.C-D).** With $k=\frac\omega c\sin\theta_0$, $q=\frac\omega c\sin\theta_s$, the mean DRC is $\langle\partial R/\partial\theta_s\rangle=\frac1{L_1}\frac{\omega}{2\pi c}\frac{\cos^2\theta_s}{\cos\theta_0}\langle|R(q|k)|^2\rangle$, and its incoherent part has $\langle|R|^2\rangle-|\langle R\rangle|^2$ in place of $\langle|R|^2\rangle$. In the radiative region $\alpha_0(q)=\sqrt{\omega^2/c^2-q^2}$ and $S(q|k)=\sqrt{\alpha_0(q)/\alpha_0(k)}\,R(q|k)$.
--   5. **Kernels with a specular part (Sec. III).** A kernel $K(q|k)=2\pi\delta(q-k)\,d(k)+r(q,k)$ is the pair $(d,r)$. For an ordinary function $N$, $\int\frac{dq}{2\pi}N(p|q)K(q|k)=N(p|k)d(k)+\int\frac{dq}{2\pi}N(p|q)r(q,k)$.
--   6. **RRE matrix elements (Sec. III.E-F).** With $\alpha(p)^2=\varepsilon\omega^2/c^2-p^2$, $\alpha_0(q)^2=\omega^2/c^2-q^2$ and $I(\gamma|Q)=\int dx_1\,e^{-i\gamma\zeta(x_1)-iQx_1}$:
--      - $M^\pm_\nu(p|q)=\pm\big[\frac{(p+\kappa q)(p-q)}{\alpha(p)\mp\alpha_0(q)}+\alpha(p)\pm\kappa\alpha_0(q)\big]I(\alpha(p)\mp\alpha_0(q)|p-q)$, with $\kappa=\varepsilon$ for $p$ and $\kappa=1$ for $s$;
--      - $N^\pm_p(p|q)=\pm\frac{pq\pm\alpha(p)\alpha_0(q)}{\alpha(p)\mp\alpha_0(q)}I(\cdot|p-q)$ and $N^\pm_s(p|q)=\pm\frac{1}{\alpha(p)\mp\alpha_0(q)}I(\cdot|p-q)$.
--
--      On a surface of length $L$, $I$ and $\tilde\zeta^{(n)}(Q)=\int dx_1\,\zeta^ne^{-iQx_1}$ are integrals over $(-L/2,L/2)$. The coefficients of the expansion of $N^\pm_\nu$ are $\mathcal N^{\pm(0)}_\nu$, the $n=0$ term, and for $n\ge1$ $\mathcal N^{\pm(n)}_p=(-i)^n[\pm pq+\alpha(p)\alpha_0(q)][\alpha(p)\mp\alpha_0(q)]^{n-1}$ and $\mathcal N^{\pm(n)}_s=\pm(-i)^n[\alpha(p)\mp\alpha_0(q)]^{n-1}$. The Fresnel coefficients are $R^{(0)}_p=\frac{\varepsilon\alpha_0-\alpha}{\varepsilon\alpha_0+\alpha}$ and $R^{(0)}_s=\frac{\alpha_0-\alpha}{\alpha_0+\alpha}$.
--   7. **Lippmann-Schwinger equation and scattering potentials (Sec. III.G-H).** $G(q|k)=2\pi\delta(q-k)G^{(0)}(k)+G^{(0)}(q)\int\frac{dp}{2\pi}V(q|p)G(p|k)$. $V^{(1)}_\nu$ and $V^{(2)}_\nu$ are the expressions (97), with arbitrary functions in place of $\tilde\zeta^{(1)},\tilde\zeta^{(2)}$.
--   8. **Double-scattering paths (Sec. IV.A.3).** In a medium of dielectric constant $\varepsilon_0$, $k_0=\sqrt{\varepsilon_0}\frac\omega c(\sin\theta_0,-\cos\theta_0)$ and $k_s=\sqrt{\varepsilon_0}\frac\omega c(\sin\theta_s,\cos\theta_s)$. A path that enters at $r_{in}$, travels to $r_{out}$ in a mode of wave number $q$ and leaves along $k_s$ has phase $k_0\cdot r_{in}+q|r_{out}-r_{in}|-k_s\cdot r_{out}$. $\Delta\phi_{nm}$ is the phase of the path $C\to B$ in mode $n$ minus that of the path $B\to C$ in mode $m$.
--   9. **Localization (Sec. IV.B).** The West-O'Donnell spectrum (139) allows momentum transfers $2k_1-\Delta k\le|Q|\le2k_1+\Delta k$. The ohmic mean free path is $\ell_\varepsilon=1/(2k_2)$. The least-squares slope of points $(x_i,y_i)$ is $\sum(x_i-\bar x)(y_i-\bar y)/\sum(x_i-\bar x)^2$.
--   10. **Correlation functions (Sec. IV.C).** $\delta S=S-\langle S\rangle$, and the fourth-order joint cumulant is $\{abcd\}=\langle a'b'c'd'\rangle-\langle a'b'\rangle\langle c'd'\rangle-\langle a'c'\rangle\langle b'd'\rangle-\langle a'd'\rangle\langle b'c'\rangle$ with $x'=x-\langle x\rangle$. The intensity correlation is $C=\frac{\varepsilon_0}{L_1^2}\frac{\omega^2}{c^2}[\langle|S_1|^2|S_2|^2\rangle-\langle|S_1|^2\rangle\langle|S_2|^2\rangle]$. Under the memory-effect condition a feature at $\theta_s$ for incidence $\theta_0$ moves, at incidence $\theta$, to $\arcsin(\sin\theta+\sin\theta_s-\sin\theta_0)$.
--
--   **Formalization Note** The paper's amplitudes for an infinite rough surface are distributions in $q$. Only their specular $\delta$-part and regular part enter here, through item 5. $I(\gamma|q)$ and $\tilde\zeta^{(n)}$ are taken over a surface of finite length $L$, the setting of the paper's numerics, where they are ordinary integrals. Where only $\alpha(q)^2=\varepsilon\omega^2/c^2-q^2$ and $\alpha_0(q)^2=\omega^2/c^2-q^2$ are used, $\alpha,\alpha_0$ are arbitrary complex functions satisfying these relations, not a fixed branch of the square root. The paper's printed normal vector $(\zeta'e_1+e_3)/\sqrt{1+\zeta'^2}$ has a sign slip. The normal used here is $(-\zeta',0,1)/\sqrt{1+\zeta'^2}$, the one for which $n\cdot\nabla$ is the paper's $\partial_n$.
-- source:
--   I. Simonsen, A random walk through surface scattering phenomena: Theory and phenomenology, arXiv:cond-mat/0408017v1 (2004), Sec. II.C-D eqs. (Elmag:BS), (17)-(21); Sec. II.G eqs. (35)-(37); Sec. III.C-H eqs. (58)-(60), (63), (78)-(84), (86), (91)-(93), (97), (100a); Sec. IV.A-C eqs. (135), (139), (142)-(145), (Eq:Phen:Rewritten)-(PHEN:Eq:CN), (151)

import Mathlib

/-!
I. Simonsen, *A random walk through surface scattering phenomena: Theory and phenomenology*,
arXiv:cond-mat/0408017v1 (2004): the objects used in the derivations of Sections II-IV.

* Sec. II.C-D: the primary field `Φ_ν` (`H₂` for `p`, `E₂` for `s`) and the fields it
  determines, the normal vector and normal derivative on `x₃ = ζ(x₁)`, the planar surface
  plasmon polariton (SPP) ansatz and the free-electron dielectric function.
* Sec. II.G: the rms height difference of a random profile.
* Sec. III: kernels of the form `2πδ(q-k) d(k) + r(q,k)`, the mean differential reflection
  coefficient (DRC), the S-matrix in the radiative region, the matrix elements of the reduced
  Rayleigh equation (RRE), their small-amplitude expansion, the Fresnel coefficients, the
  Lippmann-Schwinger equation and the first two orders of the scattering potential.
* Sec. IV: the phases of double-scattering paths, the support of the West-O'Donnell power
  spectrum, the least-squares slope, and the angular intensity correlation function.

Coordinates `(x₁, x₂, x₃)` of vectors in `Fin 3 → ℂ` are the indices `0, 1, 2`. `α(q)` and
`α₀(q)` denote the vertical wave numbers in the lower medium and in vacuum,
`α(q)² = ε (ω/c)² - q²` and `α₀(q)² = (ω/c)² - q²`; where only these relations are used, they
are hypotheses on arbitrary complex numbers rather than a fixed branch of the square root.
-/

open MeasureTheory Complex

noncomputable section

namespace CondMat0408017

/-! ### Sec. II.C: boundary conditions for the primary field -/

/-- The two linear polarizations `ν = p, s` (Sec. II.C.1). -/
inductive Polarization
  | p
  | s

/-- The unit normal `n = (-ζ', 0, 1)/√(1 + ζ'²)` to the interface `x₃ = ζ(x₁)` at a point where
`ζ'(x₁) = dζ`, directed into medium `+` (Sec. II.C.1; it is the vector for which
`n · ∇ = ∂_n` of eq. (Elmag:normal-derivative)). -/
def surfaceNormal (dζ : ℝ) : Fin 3 → ℂ :=
  ((Real.sqrt (1 + dζ ^ 2))⁻¹ : ℂ) • ![-(dζ : ℂ), 0, 1]

/-- The normal derivative `∂_n Φ = (-ζ' ∂_{x₁}Φ + ∂_{x₃}Φ)/√(1 + ζ'²)` of eq.
(Elmag:normal-derivative), from the partial derivatives `d1 = ∂_{x₁}Φ`, `d3 = ∂_{x₃}Φ`. -/
def normalDeriv (dζ : ℝ) (d1 d3 : ℂ) : ℂ :=
  (-(dζ : ℂ) * d1 + d3) / (Real.sqrt (1 + dζ ^ 2) : ℂ)

/-- The fields `(E, H)` at a point, determined by the value `Φ` of the primary field and its
partial derivatives `d1 = ∂_{x₁}Φ`, `d3 = ∂_{x₃}Φ` (eqs. (Elmag:Primary-fields),
(Elmag:BS:p-pol), (Elmag:BS:s-pol)). For `p`: `H = (0, Φ, 0)`,
`E = (-(i/ωε) ∂₃Φ, 0, (i/ωε) ∂₁Φ)`. For `s`: `E = (0, Φ, 0)`,
`H = ((i/ωμ) ∂₃Φ, 0, -(i/ωμ) ∂₁Φ)`. Here `κ = ε` for `p` and `κ = μ` for `s`. -/
def emFields (ν : Polarization) (ω : ℝ) (κ Φ d1 d3 : ℂ) : (Fin 3 → ℂ) × (Fin 3 → ℂ) :=
  match ν with
  | .p => (![-(I / ((ω : ℂ) * κ)) * d3, 0, (I / ((ω : ℂ) * κ)) * d1], ![0, Φ, 0])
  | .s => (![0, Φ, 0], ![(I / ((ω : ℂ) * κ)) * d3, 0, -(I / ((ω : ℂ) * κ)) * d1])

/-! ### Sec. II.D: surface plasmon polaritons at a planar interface -/

/-- The decay constant `β(ω) = √(k² - ε (ω/c)²)` of eq. (Elmag:beta-def), for a real dielectric
constant `ε`. -/
def decayConst (eps k ω c : ℝ) : ℝ :=
  Real.sqrt (k ^ 2 - eps * (ω / c) ^ 2)

/-- The surface-localized field above the planar interface (`x₃ > 0`),
`Φ⁺(x₁, x₃) = A⁺ e^{-β₊ x₃} e^{ikx₁}` (eq. (Elmag:SPP-fields)). -/
def planarModeUpper (A : ℂ) (β k : ℝ) (x1 x3 : ℝ) : ℂ :=
  A * cexp (-(β : ℂ) * x3) * cexp (I * k * x1)

/-- The surface-localized field below the planar interface (`x₃ < 0`),
`Φ⁻(x₁, x₃) = A⁻ e^{β₋ x₃} e^{ikx₁}` (eq. (Elmag:SPP-fields)). -/
def planarModeLower (A : ℂ) (β k : ℝ) (x1 x3 : ℝ) : ℂ :=
  A * cexp ((β : ℂ) * x3) * cexp (I * k * x1)

/-- The boundary conditions (Elmag:BCSa), (Elmag:BCSb) on the planar interface `x₃ = 0`, where
`∂_n = ∂_{x₃}`: `Φ⁺ = Φ⁻` and `(1/κ⁺) ∂_{x₃}Φ⁺ = (1/κ⁻) ∂_{x₃}Φ⁻` at every point `x₁`. -/
def FlatInterfaceBC (κP κM : ℂ) (ΦP ΦM : ℝ → ℝ → ℂ) : Prop :=
  ∀ x1 : ℝ, ΦP x1 0 = ΦM x1 0 ∧ deriv (ΦP x1) 0 / κP = deriv (ΦM x1) 0 / κM

/-- A `p`-polarized surface plasmon polariton of wave number `k` and frequency `ω` exists at the
planar interface between media of real dielectric constants `ε₊` (above) and `ε₋` (below)
(Sec. II.D.1): both decay constants are real and positive, and the boundary conditions with
`κ^± = ε_±` have a non-zero solution of the form (Elmag:SPP-fields). -/
def IsPlanarSPP (epsP epsM k ω c : ℝ) : Prop :=
  0 < k ^ 2 - epsP * (ω / c) ^ 2 ∧ 0 < k ^ 2 - epsM * (ω / c) ^ 2 ∧
    ∃ AP AM : ℂ, (AP ≠ 0 ∨ AM ≠ 0) ∧
      FlatInterfaceBC epsP epsM (planarModeUpper AP (decayConst epsP k ω c) k)
        (planarModeLower AM (decayConst epsM k ω c) k)

/-- The dielectric function of a free-electron metal, `ε(ω) = ε_∞ (1 - ω_p²/ω²)`
(eq. (Elmag:eps-free-electron-metal)), with background dielectric constant `ε_∞` and plasma
frequency `ω_p`. -/
def freeElectronEps (epsInf ωp ω : ℝ) : ℝ :=
  epsInf * (1 - ωp ^ 2 / ω ^ 2)

/-- The SPP frequency of eq. (Elmag:SPP-free-metal),
`ω_sp(k) = [½(k²c²(1+ε_∞)/ε_∞ + ω_p²) - ½√((k²c²(1+ε_∞)/ε_∞ + ω_p²)² - 4k²c²ω_p²)]^{1/2}`. -/
def omegaSP (epsInf ωp c k : ℝ) : ℝ :=
  Real.sqrt (1 / 2 * (k ^ 2 * c ^ 2 / epsInf * (1 + epsInf) + ωp ^ 2) -
    1 / 2 * Real.sqrt ((k ^ 2 * c ^ 2 / epsInf * (1 + epsInf) + ωp ^ 2) ^ 2 -
      4 * k ^ 2 * c ^ 2 * ωp ^ 2))

/-! ### Sec. II.G: self-affine surfaces -/

/-- The rms height difference `σ(Δx₁) = ⟨(ζ(x₁ + Δx₁) - ζ(x₁))²⟩^{1/2}` of eq.
(Eq:CHAR:rms-top) for a random profile `ζ(x₁, ·)` on a probability space, evaluated at the base
point `x₁ = 0`; for a profile with stationary increments it does not depend on the base point. -/
def rmsHeightDiff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ζ : ℝ → Ω → ℝ) (Δ : ℝ) : ℝ :=
  Real.sqrt (∫ w, (ζ Δ w - ζ 0 w) ^ 2 ∂P)

/-! ### Sec. III.C-D: mean differential reflection coefficient, S-matrix -/

/-- The mean differential reflection coefficient of eq. (Theory:meanDRC-total),
`⟨∂R/∂θ_s⟩ = (1/L₁)(ω/2πc)(cos²θ_s/cos θ₀) ⟨|R(q|k)|²⟩`, where `Rq` is the random amplitude
`R(q|k)` at `k = (ω/c) sin θ₀`, `q = (ω/c) sin θ_s`. -/
def meanDRC {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (L1 ω c θ0 θs : ℝ) (Rq : Ω → ℂ) : ℝ :=
  1 / L1 * (ω / (2 * Real.pi * c)) * (Real.cos θs ^ 2 / Real.cos θ0) * ∫ w, ‖Rq w‖ ^ 2 ∂P

/-- The incoherent part of the mean DRC, eq. (Theory:meanDRC-incohr):
`(1/L₁)(ω/2πc)(cos²θ_s/cos θ₀) [⟨|R(q|k)|²⟩ - |⟨R(q|k)⟩|²]`. -/
def incoherentMeanDRC {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (L1 ω c θ0 θs : ℝ)
    (Rq : Ω → ℂ) : ℝ :=
  1 / L1 * (ω / (2 * Real.pi * c)) * (Real.cos θs ^ 2 / Real.cos θ0) *
    ((∫ w, ‖Rq w‖ ^ 2 ∂P) - ‖∫ w, Rq w ∂P‖ ^ 2)

/-- `α₀(q) = √((ω/c)² - q²)` in the radiative region `|q| ≤ ω/c`, with `wv = ω/c`
(eq. (47)). -/
def alpha0Rad (wv q : ℝ) : ℝ :=
  Real.sqrt (wv ^ 2 - q ^ 2)

/-- The scattering matrix `S(q|k) = √(α₀(q)/α₀(k)) R(q|k)` of eq. (Theory:Eq:S-matrix-def), for
`|q|, |k| < ω/c`, `wv = ω/c`; `R` is the function `q ↦ R(q|k)`. -/
def sMatrixRad (wv k : ℝ) (R : ℝ → ℂ) (q : ℝ) : ℂ :=
  (Real.sqrt (alpha0Rad wv q / alpha0Rad wv k) : ℂ) * R q

/-! ### Sec. III: kernels with a specular part -/

/-- A kernel `K(q|k) = 2π δ(q - k) d(k) + r(q, k)`: the specular (δ-function) part with
coefficient `d = diag` and the regular part `r = reg`. Scattering amplitudes, Green's functions
and their zeroth-order terms in Sec. III have this form (eqs. (86a), (91), (100a)). -/
structure DKernel where
  diag : ℝ → ℂ
  reg : ℝ → ℝ → ℂ

/-- `∫ dq/2π N(p|q) K(q|k)` for an ordinary function `N` and a kernel `K` with specular part:
the δ-function contributes `N(p|k) d(k)`, the regular part `∫ dq/2π N(p|q) r(q, k)`. -/
def DKernel.applyLeft (N : ℝ → ℝ → ℂ) (K : DKernel) (p k : ℝ) : ℂ :=
  N p k * K.diag k + ∫ q, N p q * K.reg q k / (2 * Real.pi)

/-! ### Sec. III.E-F: reduced Rayleigh equation and small-amplitude perturbation theory -/

/-- The prefactor of `M^±_ν(p|q)` in eq. (Theory:RRE-matrix-elements),
`±[(p + κ q)(p - q)/(α(p) ∓ α₀(q)) + α(p) ± κ α₀(q)]`, with `sgn = ±1`, `a = α(p)`,
`a0 = α₀(q)`. The full matrix element is this times `I(α(p) ∓ α₀(q) | p - q)`. -/
def rreM (κ sgn : ℂ) (p q : ℝ) (a a0 : ℂ) : ℂ :=
  sgn * (((p : ℂ) + κ * q) * ((p : ℂ) - q) / (a - sgn * a0) + a + sgn * κ * a0)

/-- The prefactor of `N^±_p(p|q)` in eq. (Theory:RRE-p-b),
`±(pq ± α(p)α₀(q))/(α(p) ∓ α₀(q))`, with `sgn = ±1`, `a = α(p)`, `a0 = α₀(q)`. -/
def rreNp (sgn : ℂ) (p q : ℝ) (a a0 : ℂ) : ℂ :=
  sgn * ((p : ℂ) * q + sgn * a * a0) / (a - sgn * a0)

/-- The prefactor of `N^±_s(p|q)` in eq. (Theory:RRE-s-b), `±1/(α(p) ∓ α₀(q))`. -/
def rreNs (sgn : ℂ) (a a0 : ℂ) : ℂ :=
  sgn / (a - sgn * a0)

/-- `I(γ|Q) = ∫ dx₁ e^{-iγζ(x₁)} e^{-iQx₁}` (eq. (Theory:zeta-int)) for a surface of length `L`,
`-L/2 < x₁ < L/2`. -/
def zetaIntL (ζ : ℝ → ℝ) (L : ℝ) (γ : ℂ) (Q : ℝ) : ℂ :=
  ∫ x in (-(L / 2))..(L / 2), cexp (-I * γ * ζ x - I * Q * x)

/-- `ζ̃^{(n)}(Q) = ∫ dx₁ ζ(x₁)ⁿ e^{-iQx₁}` (eq. (Theory:int-expansion)) for a surface of length
`L`. -/
def zetaPowFT (ζ : ℝ → ℝ) (L : ℝ) (n : ℕ) (Q : ℝ) : ℂ :=
  ∫ x in (-(L / 2))..(L / 2), (ζ x : ℂ) ^ n * cexp (-I * Q * x)

/-- The expansion coefficients `𝒩^{±(n)}_p(p|q)` of eq. (Eq:Theorey:SMPT:N-expansion):
for `n ≥ 1`, `(-i)ⁿ [±pq + α(p)α₀(q)] [α(p) ∓ α₀(q)]^{n-1}`; for `n = 0`, the `n = 0` term of the
expansion of `N^±_p`, `±(pq ± α(p)α₀(q))/(α(p) ∓ α₀(q))`. -/
def rreNpCoeff (sgn : ℂ) (n : ℕ) (p q : ℝ) (a a0 : ℂ) : ℂ :=
  if n = 0 then rreNp sgn p q a a0
  else (-I) ^ n * (sgn * p * q + a * a0) * (a - sgn * a0) ^ (n - 1)

/-- The expansion coefficients `𝒩^{±(n)}_s(p|q)` of eq. (Eq:Theorey:SMPT:N-expansion):
for `n ≥ 1`, `±(-i)ⁿ [α(p) ∓ α₀(q)]^{n-1}`; for `n = 0`, `±1/(α(p) ∓ α₀(q))`. -/
def rreNsCoeff (sgn : ℂ) (n : ℕ) (a a0 : ℂ) : ℂ :=
  if n = 0 then rreNs sgn a a0 else sgn * (-I) ^ n * (a - sgn * a0) ^ (n - 1)

/-- The Fresnel coefficient for `p` polarization with vacuum above (`ε₀ = 1`),
`(ε α₀(k) - α(k))/(ε α₀(k) + α(k))` (eq. (Theory:Fresnel)). -/
def fresnelP (eps a a0 : ℂ) : ℂ :=
  (eps * a0 - a) / (eps * a0 + a)

/-- The Fresnel coefficient for `s` polarization, `(α₀(k) - α(k))/(α₀(k) + α(k))`
(eq. (Theory:Fresnel)). -/
def fresnelS (a a0 : ℂ) : ℂ :=
  (a0 - a) / (a0 + a)

/-! ### Sec. III.G-H: transition matrix, scattering potential, renormalized Green's function -/

/-- The Lippmann-Schwinger equation (Theory:Rough-green-a) for the renormalized Green's function,
`G(q|k) = 2πδ(q - k) G⁰(k) + G⁰(q) ∫ dp/2π V(q|p) G(p|k)`, for `G` with a specular part and a
regular scattering potential `V`: its specular part is `G⁰`, and its regular part satisfies
`r(q, k) = G⁰(q) [V(q|k) d(k) + ∫ dp/2π V(q|p) r(p, k)]`. -/
def IsLippmannSchwinger (G0 : ℝ → ℂ) (V : ℝ → ℝ → ℂ) (G : DKernel) : Prop :=
  (∀ k, G.diag k = G0 k) ∧ ∀ q k, G.reg q k = G0 q * DKernel.applyLeft V G q k

/-- The first-order scattering potential `V^{(1)}_ν(q|k)` of eq. (Eq:Scattering-pot), quoted from
Maradudin and Méndez (1993): `i (ε-1)/ε² [ε qk - α(q)α(k)] ζ̃⁽¹⁾(q-k)` for `p` and
`i (ω/c)² (ε-1) ζ̃⁽¹⁾(q-k)` for `s`; `wv = ω/c`, `ζ1 = ζ̃⁽¹⁾`. -/
def scatPotV1 (ν : Polarization) (eps : ℂ) (wv : ℝ) (α : ℝ → ℂ) (ζ1 : ℝ → ℂ) (q k : ℝ) : ℂ :=
  match ν with
  | .p => I * (eps - 1) / eps ^ 2 * (eps * q * k - α q * α k) * ζ1 (q - k)
  | .s => I * (wv : ℂ) ^ 2 * (eps - 1) * ζ1 (q - k)

/-- The second-order scattering potential `V^{(2)}_ν(q|k)` of eq. (Eq:Scattering-pot):
for `p`, `i (ε-1)/ε² [α(q)+α(k)][qk - α(q)α(k)] ζ̃⁽²⁾(q-k)
+ 2i (ε-1)²/ε³ α(q) ∫ dp/2π ζ̃⁽¹⁾(q-p) α(p) ζ̃⁽¹⁾(p-k) α(k)`; for `s`,
`i (ω/c)² (ε-1) [α(q)+α(k)] ζ̃⁽²⁾(q-k)`; `ζ1 = ζ̃⁽¹⁾`, `ζ2 = ζ̃⁽²⁾`. -/
def scatPotV2 (ν : Polarization) (eps : ℂ) (wv : ℝ) (α : ℝ → ℂ) (ζ1 ζ2 : ℝ → ℂ) (q k : ℝ) : ℂ :=
  match ν with
  | .p => I * (eps - 1) / eps ^ 2 * (α q + α k) * ((q : ℂ) * k - α q * α k) * ζ2 (q - k) +
      2 * I * (eps - 1) ^ 2 / eps ^ 3 * α q *
        (∫ p, ζ1 (q - p) * α p * ζ1 (p - k) / (2 * Real.pi)) * α k
  | .s => I * (wv : ℂ) ^ 2 * (eps - 1) * (α q + α k) * ζ2 (q - k)

/-! ### Sec. IV.A: phases of double-scattering paths -/

/-- The wave vector `k₀ = √ε₀ (ω/c) (sin θ₀, -cos θ₀)` of the incident wave in the `(x₁, x₃)`
plane (incident medium of dielectric constant `ε₀`). -/
def incWaveVec (eps0 ω c θ0 : ℝ) : ℝ × ℝ :=
  (Real.sqrt eps0 * (ω / c) * Real.sin θ0, -(Real.sqrt eps0 * (ω / c) * Real.cos θ0))

/-- The wave vector `k_s = √ε₀ (ω/c) (sin θ_s, cos θ_s)` of the scattered wave. -/
def scatWaveVec (eps0 ω c θs : ℝ) : ℝ × ℝ :=
  (Real.sqrt eps0 * (ω / c) * Real.sin θs, Real.sqrt eps0 * (ω / c) * Real.cos θs)

/-- The Euclidean dot product on `ℝ × ℝ`. -/
def dot2 (u v : ℝ × ℝ) : ℝ :=
  u.1 * v.1 + u.2 * v.2

/-- The Euclidean length on `ℝ × ℝ`. -/
def eucl (u : ℝ × ℝ) : ℝ :=
  Real.sqrt (u.1 ^ 2 + u.2 ^ 2)

/-- The phase of a double-scattering path (Fig. (Fig:Phen:scat-path)) that enters at the
scattering centre `rIn`, travels to the centre `rOut` in a guided (or surface) mode of wave number
`q`, and leaves in the direction of `k_s`: `k₀ · rIn + q |rOut - rIn| - k_s · rOut`. -/
def pathPhase (k0 ks : ℝ × ℝ) (q : ℝ) (rIn rOut : ℝ × ℝ) : ℝ :=
  dot2 k0 rIn + q * eucl (rOut - rIn) - dot2 ks rOut

/-- The phase difference `Δφ_{nm}` between the double-scattering path `ĀCBD̄`, which visits `C`
then `B` through mode `n` of wave number `qn`, and the path `ABCD`, which visits `B` then `C`
through mode `m` of wave number `qm` (Sec. IV.A.3); the incident and scattered directions are
`θ₀` and `θ_s` in a medium of dielectric constant `ε₀`. -/
def doublePathPhaseDiff (eps0 ω c θ0 θs qn qm : ℝ) (rB rC : ℝ × ℝ) : ℝ :=
  pathPhase (incWaveVec eps0 ω c θ0) (scatWaveVec eps0 ω c θs) qn rC rB -
    pathPhase (incWaveVec eps0 ω c θ0) (scatWaveVec eps0 ω c θs) qm rB rC

/-! ### Sec. IV.C: memory effect -/

/-- The scattering angle `θ'_s = arcsin(sin θ + sin θ_s - sin θ₀)` to which a speckle feature at
`θ_s` for incidence `θ₀` moves when the angle of incidence becomes `θ`, under the condition of
equal momentum transfer `q' - k' = q - k` (eq. (PHEN:Eq:C1_condition)), with
`k = √ε₀ (ω/c) sin θ₀`, `q = √ε₀ (ω/c) sin θ_s` (eq. (151)). -/
def memoryShiftAngle (θ0 θs θ : ℝ) : ℝ :=
  Real.arcsin (Real.sin θ + (Real.sin θs - Real.sin θ0))

/-! ### Sec. IV.B: localization of surface plasmon polaritons -/

/-- The momentum transfers allowed by the West-O'Donnell power spectrum (Eq:Loc:power) of width
`2Δk` centred at `±2k₁`: `k₋ ≤ |Q| ≤ k₊` with `k_± = 2k₁ ± Δk`. -/
def westODonnellSupport (k1 Δk : ℝ) : Set ℝ :=
  {Q | 2 * k1 - Δk ≤ |Q| ∧ |Q| ≤ 2 * k1 + Δk}

/-- The ohmic mean free path `ℓ_ε(ω) = 1/(2k₂(ω))` of an SPP with `Im k_sp = k₂`
(Sec. IV.B.3). -/
def ohmicMeanFreePath (k2 : ℝ) : ℝ :=
  1 / (2 * k2)

/-- The slope of the least-squares straight line through the points `(x i, y i)`. -/
def olsSlope {m : ℕ} (x y : Fin m → ℝ) : ℝ :=
  (∑ i, (x i - (∑ j, x j) / m) * (y i - (∑ j, y j) / m)) / ∑ i, (x i - (∑ j, x j) / m) ^ 2

/-! ### Sec. IV.C: angular intensity correlation functions -/

/-- The incoherent component `δS = S - ⟨S⟩` of a random amplitude. -/
def fluct {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (S : Ω → ℂ) : Ω → ℂ :=
  fun w => S w - ∫ v, S v ∂P

/-- The fourth-order joint cumulant
`{abcd} = ⟨a'b'c'd'⟩ - ⟨a'b'⟩⟨c'd'⟩ - ⟨a'c'⟩⟨b'd'⟩ - ⟨a'd'⟩⟨b'c'⟩` of complex random variables,
where `x' = x - ⟨x⟩`. -/
def cumulant4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (a b c d : Ω → ℂ) : ℂ :=
  let a' := fluct P a
  let b' := fluct P b
  let c' := fluct P c
  let d' := fluct P d
  (∫ w, a' w * b' w * c' w * d' w ∂P) - (∫ w, a' w * b' w ∂P) * (∫ w, c' w * d' w ∂P) -
    (∫ w, a' w * c' w ∂P) * (∫ w, b' w * d' w ∂P) - (∫ w, a' w * d' w ∂P) * (∫ w, b' w * c' w ∂P)

/-- The angular intensity correlation function of eq. (Eq:Phen:Rewritten),
`C(q,k|q',k') = (ε₀/L₁²)(ω/c)² [⟨|S(q|k)|² |S(q'|k')|²⟩ - ⟨|S(q|k)|²⟩⟨|S(q'|k')|²⟩]`, with
`S1 = S(q|k)`, `S2 = S(q'|k')` and `wv = ω/c`. -/
def intensityCorrelation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (eps0 L1 wv : ℝ)
    (S1 S2 : Ω → ℂ) : ℝ :=
  eps0 / L1 ^ 2 * wv ^ 2 *
    ((∫ w, ‖S1 w‖ ^ 2 * ‖S2 w‖ ^ 2 ∂P) - (∫ w, ‖S1 w‖ ^ 2 ∂P) * ∫ w, ‖S2 w‖ ^ 2 ∂P)

end CondMat0408017


