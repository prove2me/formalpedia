-- Prove2me | Definitions.Def_Arxiv1507_03491_Basic
-- name    : Arxiv1507_03491_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T16:01:26.613652+00:00
-- url     : https://prove2.me/theorems/0517000b-0072-4ad4-8cef-3e68034a519f
-- title:
--   Windows, Sommerfeld densities, Helmholtz Green's function and layer potentials of the hybrid representation
-- statement:
--   Objects of Sections 1–3 and 5 of Lai, Greengard and O'Neil (2015). Points of the plane are $\mathbf x=(x,y)$; the interface $\Gamma$ is the line $y=0$ with unit normal $\mathbf n=(0,1)$, and $\Gamma_0=(-M_0,M_0)$ is the window segment. The Helmholtz parameter satisfies $\operatorname{Re}k>0$, $\operatorname{Im}k\ge0$.
--
--   1. **Windows (eqs. 2.8–2.11).** $\Psi(x)=e^{-1/(1-x^2)}$ for $|x|<1$ and $0$ otherwise; $A=\int_0^1\Psi$; $\Phi(x)=A^{-1}\int_0^x\Psi$; the bump window is $W_{M_0}(x)=\tfrac12\big(\Phi(x+M_0/2)-\Phi(x-M_0/2)\big)$. With $\operatorname{erf}(x)=\frac{2}{\sqrt\pi}\int_0^xe^{-t^2}dt$, the window used in practice is $\tilde W_{M_0}(x)=\tfrac12\big(\operatorname{erf}(x+M_0/2)-\operatorname{erf}(x-M_0/2)\big)$.
--   2. **Fourier transform and decay.** $\hat f(\lambda)=\int_{\mathbb R}f(x)e^{-i\lambda x}\,dx$. A function $F$ decays superalgebraically if for every $n\in\mathbb N$ there are $C,R$ with $|\lambda|^n|F(\lambda)|\le C$ for $|\lambda|\ge R$; a family $F_h$, $h\in s$, does so independently of $h$ if $C,R$ can be chosen the same for all $h\in s$.
--   3. **Square root and source spectrum (eq. 2.3).** $\sqrt{\lambda^2-k^2}:=-i\,(k^2-\lambda^2)^{1/2}$ (principal power): it is positive for real $|\lambda|>k$, equals $-i\sqrt{k^2-\lambda^2}$ for real $|\lambda|<k$, and has nonnegative real part. The spectrum of a source at $(x_0,y_0)$ is $F_{x_0,y_0}(\lambda)=e^{-\sqrt{\lambda^2-k^2}\,y_0}e^{-i\lambda x_0}/\sqrt{\lambda^2-k^2}$.
--   4. **Dirichlet Sommerfeld density (eq. 2.13).** $\hat\xi_W(\lambda)=-2\,\big[\widehat{(1-W)}*F_{x_0,y_0}\big](\lambda)=-2\Big(F_{x_0,y_0}(\lambda)-\frac1{2\pi}\int_{\mathbb R}\hat W(\lambda-\mu)F_{x_0,y_0}(\mu)\,d\mu\Big)$ with $W=W_{M_0}$.
--   5. **Green's function (eq. 2.1).** $J_0(z)=\sum_{m\ge0}(-1)^m(z/2)^{2m}/(m!)^2$, $Y_0(z)=\frac2\pi\big(\log\frac z2+\gamma\big)J_0(z)+\frac2\pi\sum_{m\ge1}(-1)^{m+1}H_m(z/2)^{2m}/(m!)^2$ (principal logarithm, harmonic numbers $H_m$, Euler's constant $\gamma$), $H_0^{(1)}=J_0+iY_0$ and $G_k(\mathbf x,\mathbf x')=\frac i4H_0^{(1)}(k|\mathbf x-\mathbf x'|)$.
--   6. **Potentials and fields.** The double-layer kernel is $\partial G_k(\mathbf x,\mathbf x')/\partial n'$ at $\mathbf x'=(x',0)$, the derivative in $y'$. The Dirichlet scattered field (eq. 2.4) is $u^s(\mathbf x)=-G_k(\mathbf x,\mathbf x_0^R)$ with $\mathbf x_0^R=(x_0,-y_0)$. The single-layer potential (eq. 3.7) is $S_{\Gamma_0}[\sigma](\mathbf x)=\int_{-M_0}^{M_0}G_k(\mathbf x,(x',0))\sigma(x')\,dx'$. For a source at $(0,h)$, the impedance data (eq. 3.4) is $g=-\partial G_k/\partial n-ik\alpha\,G_k$ on $\Gamma$.
--
--   **Formalization Note** Mathlib has no Bessel or Hankel functions, so $H_0^{(1)}$ is defined by its power series (DLMF 10.2.2, 10.8.2). The distribution $\widehat{1-W}$ in (2.13) is read as $2\pi\delta-\hat W$, and the convolution as $(a*b)(\lambda)=\frac1{2\pi}\int a(\lambda-\mu)b(\mu)\,d\mu$, the normalization for which $\widehat{fg}=\hat f*\hat g$. All integrals are Lebesgue integrals; each one used in a statement converges absolutely.
-- source:
--   Lai, Greengard and O'Neil, A new hybrid integral representation for frequency domain scattering in layered media, arXiv:1507.03491v2 (2015), Section 1; Section 2, eqs. (2.1)-(2.13); Section 3, eqs. (3.3)-(3.7); Section 5

import Mathlib

/-!
Lai, Greengard and O'Neil, *A new hybrid integral representation for frequency domain scattering
in layered media*, arXiv:1507.03491v2 (2015): the window functions, Fourier transform, free-space
Helmholtz Green's function, Sommerfeld spectral density, layer potentials on the window segment
`Γ₀ = (-M₀, M₀)` and the decay notion of Sections 2, 3 and 5.

Points of the plane are written by their coordinates `(x, y)`; the interface `Γ` is the line
`y = 0` with unit normal `n = (0, 1)` (Section 1).
-/

noncomputable section

namespace Arxiv1507_03491

/-- Section 2, display before eq. (2.9): the standard bump function
`Ψ(x) = exp(-1 / (1 - x²))` for `|x| < 1` and `Ψ(x) = 0` otherwise. -/
def bumpPsi (x : ℝ) : ℝ :=
  if |x| < 1 then Real.exp (-1 / (1 - x ^ 2)) else 0

/-- Section 2, before eq. (2.9): the normalising constant `A = ∫₀¹ Ψ(t) dt`. -/
def bumpA : ℝ := ∫ t in (0 : ℝ)..1, bumpPsi t

/-- Section 2, before eq. (2.9): `Φ(x) = (1/A) ∫₀ˣ Ψ(t) dt`. -/
def bumpPhi (x : ℝ) : ℝ := (1 / bumpA) * ∫ t in (0 : ℝ)..x, bumpPsi t

/-- Eq. (2.9): the window function `W_{M₀}(x) = (Φ(x + M₀/2) - Φ(x - M₀/2)) / 2`. -/
def window (M0 x : ℝ) : ℝ := (1 / 2) * (bumpPhi (x + M0 / 2) - bumpPhi (x - M0 / 2))

/-- Eq. (2.11) (Remark 2): the error function `erf(x) = (2/√π) ∫₀ˣ e^{-t²} dt`. -/
def erf (x : ℝ) : ℝ := 2 / Real.sqrt Real.pi * ∫ t in (0 : ℝ)..x, Real.exp (-t ^ 2)

/-- Eq. (2.10) (Remark 2): the window used in practice,
`W̃_{M₀}(x) = (erf(x + M₀/2) - erf(x - M₀/2)) / 2`. -/
def erfWindow (M0 x : ℝ) : ℝ := (1 / 2) * (erf (x + M0 / 2) - erf (x - M0 / 2))

/-- Section 2, display after eq. (2.13): the Fourier transform
`f̂(λ) = ∫_{-∞}^{∞} f(x) e^{-iλx} dx` (a Lebesgue integral). -/
def fourierT (f : ℝ → ℂ) (lam : ℝ) : ℂ :=
  ∫ x : ℝ, f x * Complex.exp (-(Complex.I * (lam : ℂ) * (x : ℂ)))

/-- Lemma 2.1, Theorems 2.2, 6.1, 6.2: `F` decays superalgebraically, i.e. faster than every
inverse power of `|λ|` as `|λ| → ∞`: for every `n` there are `C, R` with `|λ|ⁿ ‖F(λ)‖ ≤ C`
whenever `|λ| ≥ R`. -/
def SuperalgDecay (F : ℝ → ℂ) : Prop :=
  ∀ n : ℕ, ∃ C R : ℝ, ∀ lam : ℝ, R ≤ |lam| → |lam| ^ n * ‖F lam‖ ≤ C

/-- Theorems 2.2, 6.1, 6.2: the family `F h` decays superalgebraically independently of the
parameter `h ∈ s`: the constants `C, R` are the same for every `h ∈ s`. -/
def SuperalgDecayUniform (F : ℝ → ℝ → ℂ) (s : Set ℝ) : Prop :=
  ∀ n : ℕ, ∃ C R : ℝ, ∀ h ∈ s, ∀ lam : ℝ, R ≤ |lam| → |lam| ^ n * ‖F h lam‖ ≤ C

/-- Eq. (2.3): the branch of `√(λ² - k²)` in the Sommerfeld integral, for `Re k > 0`,
`Im k ≥ 0` and real `λ`: `√(λ² - k²) = -i (k² - λ²)^{1/2}` with the principal power. It is
positive for real `|λ| > k`, equals `-i√(k² - λ²)` for real `|λ| < k`, and has nonnegative real
part. -/
def sqrtLK (k : ℂ) (lam : ℝ) : ℂ :=
  -Complex.I * (k ^ 2 - (lam : ℂ) ^ 2) ^ (1 / 2 : ℂ)

/-- Section 2, text before Figure 2 and eq. (2.13): the spectral function
`e^{-√(λ²-k²) y₀} e^{-iλx₀} / √(λ²-k²)` of a source at `(x₀, y₀)`. -/
def sourceSpectrum (k : ℂ) (x0 y0 lam : ℝ) : ℂ :=
  Complex.exp (-(sqrtLK k lam) * (y0 : ℂ)) / sqrtLK k lam *
    Complex.exp (-(Complex.I * (lam : ℂ) * (x0 : ℂ)))

/-- Eq. (2.13): the Sommerfeld density of the Dirichlet problem,
`ξ̂_W(λ) = -2 [(1 - W)^ ∗ F](λ)` with `F = sourceSpectrum`, where `(1 - W)^ = 2πδ - Ŵ` and the
convolution is `(a ∗ b)(λ) = (1/2π) ∫ a(λ - μ) b(μ) dμ`; thus
`ξ̂_W(λ) = -2 (F(λ) - (1/2π) ∫ Ŵ(λ - μ) F(μ) dμ)`, with `W = W_{M₀}` of eq. (2.9). -/
def dirSommerfeldDensity (M0 : ℝ) (k : ℂ) (x0 y0 lam : ℝ) : ℂ :=
  -2 * (sourceSpectrum k x0 y0 lam -
    (1 / (2 * (Real.pi : ℂ))) *
      ∫ mu : ℝ, fourierT (fun x => (window M0 x : ℂ)) (lam - mu) * sourceSpectrum k x0 y0 mu)

/-- Eq. (2.1): the Bessel function `J₀(z) = ∑_{m ≥ 0} (-1)^m (z/2)^{2m} / (m!)²`
(DLMF 10.2.2). -/
def besselJ0 (z : ℂ) : ℂ :=
  ∑' m : ℕ, (-1 : ℂ) ^ m * (z / 2) ^ (2 * m) / ((m.factorial : ℂ) ^ 2)

/-- Eq. (2.1): the Bessel function of the second kind
`Y₀(z) = (2/π)(log(z/2) + γ) J₀(z) + (2/π) ∑_{m ≥ 1} (-1)^{m+1} H_m (z/2)^{2m} / (m!)²`,
with `H_m` the harmonic numbers, `γ` Euler's constant and the principal logarithm
(DLMF 10.8.2). -/
def besselY0 (z : ℂ) : ℂ :=
  (2 / (Real.pi : ℂ)) * ((Complex.log (z / 2) + (Real.eulerMascheroniConstant : ℂ)) * besselJ0 z) +
    (2 / (Real.pi : ℂ)) *
      ∑' m : ℕ, (-1 : ℂ) ^ (m + 1) * (harmonic m : ℂ) * (z / 2) ^ (2 * m) / ((m.factorial : ℂ) ^ 2)

/-- Eq. (2.1): the Hankel function of the first kind and order zero, `H₀^{(1)} = J₀ + i Y₀`. -/
def hankel0 (z : ℂ) : ℂ := besselJ0 z + Complex.I * besselY0 z

/-- Eq. (2.1): the free-space Green's function `G_k(x, x') = (i/4) H₀^{(1)}(k |x - x'|)` for
`x = (x, y)` and `x' = (x', y')`. -/
def greenK (k : ℂ) (x y x' y' : ℝ) : ℂ :=
  Complex.I / 4 * hankel0 (k * (Real.sqrt ((x - x') ^ 2 + (y - y') ^ 2) : ℂ))

/-- Eqs. (2.6) and (2.12): the double-layer kernel `∂G_k(x, x')/∂n'` at a point `x' = (x', 0)`
of `Γ`, the derivative taken in the second variable along `n' = (0, 1)`. -/
def dlKernel (k : ℂ) (x y x' : ℝ) : ℂ :=
  deriv (fun t : ℝ => greenK k x y x' t) 0

/-- Eq. (2.4): the scattered field of the sound-soft (Dirichlet) half-space for a source at
`x₀ = (x₀, y₀)`, `y₀ > 0`: `u^s(x) = -(i/4) H₀^{(1)}(k |x - x₀^R|)` with `x₀^R = (x₀, -y₀)`. -/
def dirScattered (k : ℂ) (x0 y0 x y : ℝ) : ℂ := -greenK k x y x0 (-y0)

/-- Eq. (3.7): the single-layer potential on `Γ₀ = (-M₀, M₀)`,
`S_{Γ₀}[σ](x) = ∫_{-M₀}^{M₀} G_k(x, (x', 0)) σ(x') dx'`, at the point `x = (x, y)`. -/
def singleLayer (k : ℂ) (M0 : ℝ) (sigma : ℝ → ℂ) (x y : ℝ) : ℂ :=
  ∫ x' in Set.Ioo (-M0) M0, greenK k x y x' 0 * sigma x'

/-- Eq. (3.4): the right-hand side `g = -∂G_k/∂n - ikα G_k` on `Γ` of the impedance problem
(3.3) for a source at `(0, h)`, evaluated at `(x, 0)`; `∂/∂n` is `∂/∂y` in the target
variable. -/
def impedanceRHS (k alpha : ℂ) (h x : ℝ) : ℂ :=
  -deriv (fun t : ℝ => greenK k x t 0 h) 0 - Complex.I * k * alpha * greenK k x 0 0 h

end Arxiv1507_03491


