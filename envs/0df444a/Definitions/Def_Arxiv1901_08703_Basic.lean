-- Prove2me | Definitions.Def_Arxiv1901_08703_Basic
-- name    : Arxiv1901_08703_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T05:28:39.271127+00:00
-- url     : https://prove2.me/theorems/f7dc2326-6fb5-5a63-948b-acf34fd71802
-- title:
--   Locally rough surface scattering (Neumann case): problem (NP), layer potentials, the space $X$ and the operators $A$, $B$
-- statement:
--   Objects of Sections 1, 2, 3.1, 4 and Remark 5.2 of Qu, Zhang and Zhang (2019), *A novel integral equation for scattering by locally rough surfaces and application to the inverse problem: the Neumann case*.
--
--   1. **Surface and incident waves.** A profile $h\in C^2(\mathbb R)$ with compact support defines the locally rough surface $\Gamma=\{(t,h(t))\}$, the domain $D_+=\{x_2>h(x_1)\}$ above it and $D_-=\{x_2<h(x_1)\}$ below it. On $\Gamma$, $ds=\sqrt{1+h'(t)^2}\,dt$ and $\nu=(-h'(t),1)/\sqrt{1+h'(t)^2}$ is the unit normal directed into $D_+$. For $k>0$ and $d\in\mathbb S^1_-=\{|d|=1,\ d_2<0\}$, the incident wave is $u^i(x;d)=e^{ikd\cdot x}$ and the wave reflected by the plane $x_2=0$ is $u^r(x;d)=e^{ik(d_1x_1-d_2x_2)}$. The Neumann data is $f=-(\partial u^i/\partial\nu+\partial u^r/\partial\nu)$. $\mathbb S^1_+=\{|x|=1,\ x_2>0\}$.
--   2. **Bessel and Hankel functions.** $J_n(r)=\sum_{m\ge0}\frac{(-1)^m}{m!(m+n)!}(r/2)^{2m+n}$ for $n\ge0$ and $J_{-n}=(-1)^nJ_n$. $Y_0(r)=\frac2\pi(\log\frac r2+\gamma_E)J_0(r)+\frac2\pi\sum_{m\ge1}(-1)^{m+1}H_m\frac{(r/2)^{2m}}{(m!)^2}$ with $H_m$ the harmonic numbers, $H_0^{(1)}=J_0+iY_0$, and $\Phi_k(x,y)=\frac i4H_0^{(1)}(k|x-y|)$ is the fundamental solution of $\Delta w+k^2w=0$.
--   3. **The Neumann problem (NP).** $u$ solves (NP) with data $f$ if $u\in C^2(D_+)$ with $\Delta u+k^2u=0$ in $D_+$; $u\in H^1_{loc}(D_+)$, i.e. $\int_{D_+\cap B_\rho}(|u|^2+|\nabla u|^2)\,dx<\infty$ for every $\rho$; $u$ satisfies the Sommerfeld radiation condition $\sqrt{|x|}\,(\partial_ru-iku)\to0$ as $|x|\to\infty$ in $D_+$; and $\partial u/\partial\nu=f$ on $\Gamma$ in the weak sense
--   $$\int_{D_+}(\nabla u\cdot\nabla\varphi-k^2u\varphi)\,dx=-\int_\Gamma f\varphi\,ds\qquad\text{for all }\varphi\in C_c^\infty(\mathbb R^2).$$
--   $F$ is the far-field pattern of $u$ on a set $A$ of directions if $u(x)=\frac{e^{ik|x|}}{\sqrt{|x|}}\big(F(\hat x)+O(|x|^{-1})\big)$ uniformly for $\hat x=x/|x|\in A$. $\lambda$ is a Dirichlet eigenvalue of $-\Delta$ in an open set $D$ if some $u\in C^2(D)\cap C(\overline D)$, not identically zero, satisfies $\Delta u+\lambda u=0$ in $D$ and $u=0$ on $\partial D$.
--   4. **Geometry of the integral equation.** $R>0$ is such that the perturbation $\{(t,h(t)):t\in\operatorname{supp}h\}$ lies in $B_R=\{|x|<R\}$. Then $\Gamma_R=\{(t,h(t)):|t|<R\}$, $\partial B_R^-=\{R(\cos\theta,\sin\theta):\pi<\theta<2\pi\}$, $D_R^-=B_R\cap D_-$, and the corners are $x_A=(-R,0)$, $x_B=(R,0)$. The auxiliary domain $\tilde D$ is a bounded open set with $\overline{\tilde D}\subset D_R^-$ whose boundary $\tilde\Gamma$ is a closed $C^2$ curve. It is given with a $2\pi$-periodic, regular, positively oriented $C^2$ parametrisation $z$, and $\nu$ on $\tilde\Gamma$ points out of $\tilde D$. On $\partial D_R^-$, $\nu$ points out of $D_R^-$.
--   5. **The space $X$.** $X=L^2(\Gamma_R)\times L^2(\partial B_R^-)\times H^{-1/2}(\tilde\Gamma)$. A density $\varphi_3\in H^{-1/2}(\tilde\Gamma)$ is represented by $b\in\ell^2(\mathbb Z)$: the Fourier coefficients of $s\mapsto\varphi_3(z(s))|z'(s)|$ are $a_n=(1+n^2)^{1/4}b_n$. Integrals over $\tilde\Gamma$ are then $\int_{\tilde\Gamma}K\varphi_3\,ds=\sum_na_n\int_0^{2\pi}K(z(s))e^{ins}\,ds$.
--   6. **Potentials and the operators $A$, $B$ (eqs. (2.10), (2.14)-(2.16), (2.35)).** The field is $u^s=\mathcal S_{k,\Gamma_R}\varphi_1+\mathcal S_{k,\partial B_R^-}\varphi_2+\mathcal S_{k,\tilde\Gamma}\varphi_3$ and its far-field pattern is $S^\infty\Phi$, where $(S^\infty_{k,I}\varphi)(\hat x)=\frac{e^{i\pi/4}}{\sqrt{8\pi k}}\int_Ie^{-ik\hat x\cdot y}\varphi(y)\,ds(y)$. The rows of $A$ are $-2K'_k$ on $\Gamma_R$, $-2(K'_k-K'^{,re}_k)$ on $\partial B_R^-$ and $-2(K'_k+i\rho S_k)$ on $\tilde\Gamma$. The third row is taken as an element of $H^{-1/2}(\tilde\Gamma)$ through its Fourier coefficients. $A_{33}$ acts on coefficients through the matrix $\frac1{2\pi}\int_0^{2\pi}\!\int_0^{2\pi}e^{-ims}|z'(s)|\big(\partial_{\nu(z(s))}\Phi_k(z(s),z(t))+i\rho\Phi_k(z(s),z(t))\big)e^{int}\,dt\,ds$. $G=(2(\partial u^i/\partial\nu+\partial u^r/\partial\nu)|_{\Gamma_R},0,0)$. $B$ is the upper-left $2\times2$ block of $A$. The corner part $\hat A^\star_{11}$ of $B$ keeps the kernel of $B$ only where $x$ and $y$ are both within distance $r$ of $x_A$, or both within $r$ of $x_B$.
--   7. **Inverse problem (Section 4).** $\mathbb R^2_+\setminus\overline{B_R}=\{x_2>0,\ |x|>R\}$. The point-source Neumann data is $f(\cdot;y)=-\partial_\nu(\Phi_k(\cdot,y)+\Phi_k(\cdot,y^{re}))$ with $y^{re}=(y_1,-y_2)$.
--   8. **Spline basis (Remark 5.2).** $\phi(t)=\sum_{j=0}^{5}\frac{(-1)^j}{4!}\binom5j(t+\frac52-j)_+^4$, $h=2R/(M+5)$, $t_i=(i+2)h-R$, and $\phi_{i,M}(t)=\phi((t-t_i)/h)$.
--
--   **Formalization Note** Points of $\mathbb R^2$ are elements of `EuclideanSpace ℝ (Fin 2)`. Functions on $\Gamma_R$ and $\partial B_R^-$ are functions of the parameters $t\in(-R,R)$ and $\theta\in(\pi,2\pi)$, with the arc-length measures $\sqrt{1+h'^2}\,dt$ and $R\,d\theta$. $L^2$ spaces are Mathlib's `Lp`, and products carry the maximum norm, which is equivalent to the paper's sum norm. A solution of (NP) is taken in its representative that is $C^2$ in $D_+$; every $H^1_{loc}$ solution has one by interior elliptic regularity. With that representative the weak gradient is the classical gradient.
-- source:
--   Qu, Zhang and Zhang, A novel integral equation for scattering by locally rough surfaces and application to the inverse problem: the Neumann case, arXiv:1901.08703v1 (2019), Sections 1, 2 (pp. 2-14), Section 3.1 (p. 15), Section 4 (pp. 18-20), Remark 5.2 (p. 22)

import Mathlib

/-!
F. Qu, B. Zhang and H. Zhang, *A novel integral equation for scattering by locally rough surfaces
and application to the inverse problem: the Neumann case*, arXiv:1901.08703v1 (2019):
the locally rough surface, the incident and reflected plane waves, the Neumann problem (NP) and
the far-field pattern of Sections 1 and 2; the fundamental solution, the layer potentials, the
space `X`, the operator `A` and the right-hand side `G` of eqs. (2.4)-(2.16); the Dirichlet
eigenvalues of Theorem 2.4 and Remark 2.5; the far-field formulas (2.5), (2.33), (2.36); the
operator `B` of Remark 2.9 and its corner split (3.1); the point sources of Section 4; and the
spline basis of Remark 5.2.

Points of `ℝ²` are elements of `EuclideanSpace ℝ (Fin 2)`; the paper's `x = (x₁, x₂)` is
`x 0 = x₁`, `x 1 = x₂`. A function on `Γ = {(t, h t)}` or on `Γ_R` is written as a function of the
parameter `t = x₁`; a function on the lower semicircle `∂B_R^-` as a function of the angle
`θ ∈ (π, 2π)`; a function (or distribution) `φ₃` on the auxiliary curve `Γ̃ = {z(s)}` through the
Fourier coefficients of `s ↦ φ₃(z(s)) |z'(s)|`.
-/

open MeasureTheory

noncomputable section

namespace Arxiv1901_08703

/-- The plane `ℝ²` with its Euclidean norm. -/
abbrev R2 := EuclideanSpace ℝ (Fin 2)

/-- The point `(a, b) ∈ ℝ²`. -/
def pt (a b : ℝ) : R2 := !₂[a, b]

/-- The Euclidean inner product `x · y = x₁ y₁ + x₂ y₂` of `ℝ²`. -/
def dot (x y : R2) : ℝ := x 0 * y 0 + x 1 * y 1

/-- Section 2, p. 4: the reflection `x^{re} = (x₁, -x₂)` of `x` about the `x₁`-axis. -/
def refl (x : R2) : R2 := pt (x 0) (-(x 1))

/-! ### Bessel functions and the fundamental solution (Section 2, p. 5; Remark 2.5, p. 13) -/

/-- The Bessel function of the first kind of order `n ∈ ℕ`,
`J_n(r) = ∑_{m ≥ 0} (-1)^m / (m! (m+n)!) (r/2)^{2m+n}` (Remark 2.5, p. 13; `J₀` enters `Φ_k`). -/
def besselJNat (n : ℕ) (r : ℝ) : ℝ :=
  ∑' m : ℕ, (-1 : ℝ) ^ m / ((m.factorial : ℝ) * ((m + n).factorial : ℝ)) * (r / 2) ^ (2 * m + n)

/-- Remark 2.5, p. 13: the Bessel function `J_n` of integer order `n`, with the standard
convention `J_{-n} = (-1)^n J_n` for `n ∈ ℕ`. -/
def besselJ (n : ℤ) (r : ℝ) : ℝ :=
  if 0 ≤ n then besselJNat n.toNat r else (-1 : ℝ) ^ n.natAbs * besselJNat n.natAbs r

/-- The Bessel function of the second kind of order zero, for `r > 0`:
`Y₀(r) = (2/π)(log(r/2) + γ) J₀(r) + (2/π) ∑_{m ≥ 1} (-1)^{m+1} H_m (r/2)^{2m} / (m!)²`,
with `H_m` the harmonic numbers and `γ` the Euler–Mascheroni constant (Section 2, p. 5,
through `Φ_k`). -/
def besselY0 (r : ℝ) : ℝ :=
  2 / Real.pi * (Real.log (r / 2) + Real.eulerMascheroniConstant) * besselJNat 0 r +
    2 / Real.pi * ∑' m : ℕ, (-1 : ℝ) ^ m * (harmonic (m + 1) : ℝ) * (r / 2) ^ (2 * (m + 1)) /
      (((m + 1).factorial : ℝ) ^ 2)

/-- The Hankel function of the first kind of order zero, `H₀^{(1)} = J₀ + i Y₀`, for `r > 0`
(Section 2, p. 5). -/
def hankel01 (r : ℝ) : ℂ := (besselJNat 0 r : ℂ) + Complex.I * (besselY0 r : ℂ)

/-- Section 2, p. 5: the fundamental solution `Φ_k(x,y) = (i/4) H₀^{(1)}(k|x-y|)` of the
Helmholtz equation `Δw + k²w = 0`, for `k > 0` and `x ≠ y`. -/
def Phi (k : ℝ) (x y : R2) : ℂ := Complex.I / 4 * hankel01 (k * ‖x - y‖)

/-- Eq. (2.7), p. 5: the normal derivative `∂Φ_k(x,y)/∂ν(x) = ∇_x Φ_k(x,y) · ν` with respect to
the first variable, at the point `x`, in the direction of the normal vector `ν` at `x`. -/
def dPhi (k : ℝ) (x nu y : R2) : ℂ := fderiv ℝ (fun w => Phi k w y) x nu

/-! ### The locally rough surface and the Neumann problem (Sections 1 and 2, pp. 1-4) -/

/-- Section 1, p. 2: `h ∈ C²(ℝ)` has compact support; `Γ = {x₂ = h(x₁)}` is a locally rough
surface. -/
def IsLocalProfile (h : ℝ → ℝ) : Prop := ContDiff ℝ 2 h ∧ HasCompactSupport h

/-- Section 1, p. 2: the domain `D_+ = {(x₁, x₂) : x₂ > h(x₁)}` above `Γ`. -/
def Dplus (h : ℝ → ℝ) : Set R2 := {x | h (x 0) < x 1}

/-- Section 2, p. 4: the domain `D_- = {(x₁, x₂) : x₂ < h(x₁)}` below `Γ`. -/
def Dminus (h : ℝ → ℝ) : Set R2 := {x | x 1 < h (x 0)}

/-- The point `(t, h(t))` of `Γ`. -/
def gPt (h : ℝ → ℝ) (t : ℝ) : R2 := pt t (h t)

/-- The arc-length density `√(1 + h'(t)²)` of `Γ` in the parameter `t = x₁`. -/
def gSpeed (h : ℝ → ℝ) (t : ℝ) : ℝ := Real.sqrt (1 + deriv h t ^ 2)

/-- Section 1, p. 2: the unit normal `ν = (-h'(t), 1)/√(1 + h'(t)²)` to `Γ` at `(t, h(t))`,
directed into `D_+`; on `Γ_R` it is the unit normal of `∂D_R^-` pointing out of `D_R^-`
(Section 2, p. 5). -/
def gNormal (h : ℝ → ℝ) (t : ℝ) : R2 := (gSpeed h t)⁻¹ • pt (-deriv h t) 1

/-- Section 1, p. 2: `d ∈ 𝕊¹_- = {x : |x| = 1, x₂ < 0}`, an incident direction. -/
def IsLowerDir (d : R2) : Prop := ‖d‖ = 1 ∧ d 1 < 0

/-- Section 1, p. 2: the upper half `𝕊¹_+ = {x : |x| = 1, x₂ > 0}` of the unit circle. -/
def upperCircle : Set R2 := {x | ‖x‖ = 1 ∧ 0 < x 1}

/-- Section 1, p. 2: the incident plane wave `u^i(x;d) = exp(i k d · x)`. -/
def uInc (k : ℝ) (d x : R2) : ℂ := Complex.exp (Complex.I * (k : ℂ) * (dot d x : ℂ))

/-- Section 1, p. 2: the wave reflected by the plane `x₂ = 0`,
`u^r(x;d) = exp(i k (x₁ sin θ + x₂ cos θ))` for `d = (sin θ, -cos θ)`, that is
`u^r(x;d) = exp(i k (d₁ x₁ - d₂ x₂))`. -/
def uRefl (k : ℝ) (d x : R2) : ℂ :=
  Complex.exp (Complex.I * (k : ℂ) * ((d 0 * x 0 - d 1 * x 1 : ℝ) : ℂ))

/-- Section 2, p. 4: the Neumann data `f = -(∂u^i/∂ν + ∂u^r/∂ν)` at the point `(t, h(t))` of `Γ`,
`ν` the unit normal directed into `D_+`. -/
def incData (k : ℝ) (d : R2) (h : ℝ → ℝ) (t : ℝ) : ℂ :=
  -(fderiv ℝ (fun x => uInc k d x + uRefl k d x) (gPt h t) (gNormal h t))

/-- `∇u(x) · ∇v(x) = ∂₁u ∂₁v + ∂₂u ∂₂v` (bilinear, without complex conjugation). -/
def gradDot (u v : R2 → ℂ) (x : R2) : ℂ :=
  fderiv ℝ u x (pt 1 0) * fderiv ℝ v x (pt 1 0) + fderiv ℝ u x (pt 0 1) * fderiv ℝ v x (pt 0 1)

/-- `|∇u(x)|² = |∂₁u(x)|² + |∂₂u(x)|²`. -/
def gradSq (u : R2 → ℂ) (x : R2) : ℝ :=
  ‖fderiv ℝ u x (pt 1 0)‖ ^ 2 + ‖fderiv ℝ u x (pt 0 1)‖ ^ 2

/-- Section 2, p. 4: `u ∈ H¹_loc(D)` for a function `u` that is `C¹` in the open set `D` (so that
its weak gradient is its classical gradient): `∫_{D ∩ B_ρ} (|u|² + |∇u|²) dx < ∞` for every
`ρ`, i.e. `u ∈ H¹(D ∩ B)` for every bounded ball `B`, up to the boundary of `D`. -/
def IsH1Loc (D : Set R2) (u : R2 → ℂ) : Prop :=
  ∀ ρ : ℝ, IntegrableOn (fun x => ‖u x‖ ^ 2 + gradSq u x) (D ∩ Metric.ball 0 ρ)

/-- Theorem 2.7, p. 13: the norm `‖u‖_{H¹(D)} = (∫_D (|u|² + |∇u|²) dx)^{1/2}`. -/
def h1Norm (D : Set R2) (u : R2 → ℂ) : ℝ := Real.sqrt (∫ x in D, ‖u x‖ ^ 2 + gradSq u x)

/-- The norm `‖f‖_{L²(Γ)} = (∫_ℝ |f(t)|² √(1 + h'(t)²) dt)^{1/2}` of a function on `Γ`
written in the parameter `t` (Theorem 2.4, eq. (2.17), and Theorem 2.7, eq. (2.32)). -/
def l2Gam (h : ℝ → ℝ) (f : ℝ → ℂ) : ℝ := Real.sqrt (∫ t, ‖f t‖ ^ 2 * gSpeed h t)

/-- A test function: `φ ∈ C_c^∞(ℝ²)`, complex valued. -/
def IsTestFn (φ : R2 → ℂ) : Prop := ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ

/-- Eq. (1.1), p. 2: `u ∈ C²(D)` and `Δu + k²u = 0` in `D`. -/
def IsHelmholtzOn (D : Set R2) (k : ℝ) (u : R2 → ℂ) : Prop :=
  ContDiffOn ℝ 2 u D ∧ ∀ x ∈ D, Laplacian.laplacian u x + (k : ℂ) ^ 2 * u x = 0

/-- Eq. (1.3), p. 2: the Sommerfeld radiation condition
`lim_{r → ∞} r^{1/2} (∂u/∂r - i k u) = 0`, `r = |x|`, `x ∈ D`, with `∂u/∂r = ∇u(x) · x/|x|`;
the limit is taken as `|x| → ∞` within `D`. -/
def IsRadiating (k : ℝ) (D : Set R2) (u : R2 → ℂ) : Prop :=
  ∀ ε > 0, ∃ ρ : ℝ, ∀ x ∈ D, ρ < ‖x‖ →
    ‖(Real.sqrt ‖x‖ : ℂ) * (fderiv ℝ u x (‖x‖⁻¹ • x) - Complex.I * (k : ℂ) * u x)‖ < ε

/-- Eq. (2.1), p. 4: the Neumann condition `∂u/∂ν = f` on `Γ` (`ν` directed into `D_+`) for
`u ∈ H¹_loc(D_+)` with `Δu + k²u = 0`, in its weak (Green's formula) form:
`∫_{D_+} (∇u · ∇φ - k² u φ) dx = -∫_Γ f φ ds` for every `φ ∈ C_c^∞(ℝ²)`. -/
def IsNeumannWeak (k : ℝ) (h : ℝ → ℝ) (f : ℝ → ℂ) (u : R2 → ℂ) : Prop :=
  ∀ φ : R2 → ℂ, IsTestFn φ →
    ∫ x in Dplus h, (gradDot u φ x - (k : ℂ) ^ 2 * u x * φ x) =
      -∫ t, f t * φ (gPt h t) * (gSpeed h t : ℂ)

/-- Section 2, p. 4: `u` solves the Neumann problem (NP) with data `f`: `u ∈ H¹_loc(D_+)`
(taken in its representative that is `C²` in `D_+`), `Δu + k²u = 0` in `D_+` (eq. (1.1)), `u`
satisfies the radiation condition (1.3), and `∂u/∂ν = f` on `Γ` (eq. (2.1)). -/
def IsNPSolution (k : ℝ) (h : ℝ → ℝ) (f : ℝ → ℂ) (u : R2 → ℂ) : Prop :=
  IsHelmholtzOn (Dplus h) k u ∧ IsH1Loc (Dplus h) u ∧ IsRadiating k (Dplus h) u ∧
    IsNeumannWeak k h f u

/-- Section 1, p. 2 and Remark 2.8, p. 14: `F` is the far-field pattern of `u` for the
observation directions in `A`: `u(x) = e^{ik|x|}/√|x| (F(x̂) + O(1/|x|))` as `|x| → ∞`,
uniformly for `x̂ = x/|x| ∈ A`. -/
def HasFarFieldOn (k : ℝ) (u : R2 → ℂ) (F : R2 → ℂ) (A : Set R2) : Prop :=
  ∃ C ρ : ℝ, 0 < ρ ∧ ∀ x : R2, ρ ≤ ‖x‖ → ‖x‖⁻¹ • x ∈ A →
    ‖u x - Complex.exp (Complex.I * (k : ℂ) * (‖x‖ : ℂ)) / (Real.sqrt ‖x‖ : ℂ) * F (‖x‖⁻¹ • x)‖ ≤
      C / (‖x‖ * Real.sqrt ‖x‖)

/-- Theorem 2.4, p. 8, and Remark 2.5, p. 13: `λ` is a Dirichlet eigenvalue of `-Δ` in the open
set `D`: there is `u ∈ C²(D) ∩ C(\overline D)`, not identically zero, with `Δu + λu = 0` in `D` and
`u = 0` on `∂D`. -/
def IsDirichletEigenvalue (D : Set R2) (lam : ℝ) : Prop :=
  ∃ u : R2 → ℂ, ContDiffOn ℝ 2 u D ∧ ContinuousOn u (closure D) ∧ (∀ x ∈ frontier D, u x = 0) ∧
    (∀ x ∈ D, Laplacian.laplacian u x + (lam : ℂ) * u x = 0) ∧ ∃ x ∈ D, u x ≠ 0

/-! ### The curve `∂D_R^-`, the auxiliary curve `Γ̃` and the space `X` (Section 2, pp. 4-7) -/

/-- Section 2, p. 4: `R > 0` and the local perturbation `Γ_p = {(x₁, h(x₁)) : x₁ ∈ supp(h)}`
lies in the open disc `B_R = {|x| < R}`. -/
def PerturbationInBall (h : ℝ → ℝ) (R : ℝ) : Prop :=
  0 < R ∧ ∀ t ∈ tsupport h, t ^ 2 + h t ^ 2 < R ^ 2

/-- Section 2, p. 4: `D_R^- = B_R ∩ D_-`. -/
def DRminus (h : ℝ → ℝ) (R : ℝ) : Set R2 := {x | x 1 < h (x 0) ∧ ‖x‖ < R}

/-- The point `R(cos θ, sin θ)` of `∂B_R`; for `π < θ < 2π` it lies on `∂B_R^-`. -/
def cPt (R θ : ℝ) : R2 := pt (R * Real.cos θ) (R * Real.sin θ)

/-- The unit normal `(cos θ, sin θ)` of `∂B_R` at `R(cos θ, sin θ)`, pointing out of `B_R`. -/
def cNormal (θ : ℝ) : R2 := pt (Real.cos θ) (Real.sin θ)

/-- Section 2, p. 4: the corner `x_A = (-R, 0)` of `∂D_R^-`. -/
def xA (R : ℝ) : R2 := pt (-R) 0

/-- Section 2, p. 4: the corner `x_B = (R, 0)` of `∂D_R^-`. -/
def xB (R : ℝ) : R2 := pt R 0

/-- Arc length on `Γ_R = {(t, h(t)) : -R < t < R}` in the parameter `t`:
`ds = √(1 + h'(t)²) dt` on `(-R, R)`. `L²(Γ_R)` is `L²` of this measure. -/
def muG (h : ℝ → ℝ) (R : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioo (-R) R)).withDensity (fun t => ENNReal.ofReal (gSpeed h t))

/-- Arc length on `∂B_R^- = {R(cos θ, sin θ) : π < θ < 2π}` in the parameter `θ`: `ds = R dθ`.
`L²(∂B_R^-)` is `L²` of this measure. -/
def muB (R : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioo Real.pi (2 * Real.pi))).withDensity (fun _ => ENNReal.ofReal R)

/-- The unit normal at `z(s)` of a positively oriented closed curve `z`:
`(z₂'(s), -z₁'(s))/|z'(s)|`, which points out of the domain the curve encloses. -/
def auxNormal (z : ℝ → R2) (s : ℝ) : R2 := ‖deriv z s‖⁻¹ • pt (deriv z s 1) (-(deriv z s 0))

/-- Section 2, p. 4: an auxiliary domain `D̃` with `\overline{D̃} ⊂ D_R^-` and `C²`-smooth boundary
`Γ̃ = ∂D̃`, given with a `2π`-periodic, regular, positively oriented `C²` parametrisation `z` of
`Γ̃` that is injective on one period. The field `outward` says that `auxNormal z` is the unit
normal pointing out of `D̃` (the normal `ν` of `Γ̃` used in eqs. (2.7), (2.13), (2.15)). -/
structure AuxDomain (h : ℝ → ℝ) (R : ℝ) where
  /-- The auxiliary domain `D̃`. -/
  D : Set R2
  /-- The parametrisation of `Γ̃ = ∂D̃`. -/
  z : ℝ → R2
  /-- `D̃` is open. -/
  isOpen_D : IsOpen D
  /-- `D̃` is bounded. -/
  isBounded_D : Bornology.IsBounded D
  /-- `z` is `2π`-periodic. -/
  periodic_z : Function.Periodic z (2 * Real.pi)
  /-- `z` is `C²`. -/
  contDiff_z : ContDiff ℝ 2 z
  /-- `z` is regular. -/
  deriv_ne : ∀ s, deriv z s ≠ 0
  /-- `z` is injective on one period. -/
  injOn_z : Set.InjOn z (Set.Ico 0 (2 * Real.pi))
  /-- `Γ̃ = ∂D̃` is the curve `z`. -/
  frontier_eq : frontier D = Set.range z
  /-- `\overline{D̃} ⊂ D_R^-`. -/
  closure_sub : closure D ⊆ DRminus h R
  /-- `auxNormal z` points out of `D̃` (positive orientation of `z`). -/
  outward : ∀ s, ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
    z s + ε • auxNormal z s ∉ closure D ∧ z s - ε • auxNormal z s ∈ D

/-- Section 2, p. 6: the space `H^{-1/2}(Γ̃)`, represented by `ℓ²(ℤ)`: `b ∈ ℓ²(ℤ)` stands for the
distribution `φ₃` on `Γ̃` such that `s ↦ φ₃(z(s)) |z'(s)|` has Fourier series
`∑_n a_n e^{ins}` with `a_n = (1 + n²)^{1/4} b_n` (so `‖b‖_{ℓ²}` is an equivalent
`H^{-1/2}(Γ̃)`-norm of `φ₃`). -/
abbrev Hm12 := lp (fun _ : ℤ => ℂ) 2

/-- The Fourier coefficients `a_n = (1 + n²)^{1/4} b_n` of `s ↦ φ₃(z(s)) |z'(s)|` for the element
`b` of `H^{-1/2}(Γ̃)` (see `Hm12`). -/
def hmhCoeff (b : Hm12) (n : ℤ) : ℂ := (((1 + (n : ℝ) ^ 2) ^ ((1 : ℝ) / 4) : ℝ) : ℂ) * b n

/-- Section 2, p. 6: `X = L²(Γ_R) × L²(∂B_R^-) × H^{-1/2}(Γ̃)` (product norm: the maximum of the
three norms, equivalent to the paper's sum). -/
abbrev Xsp (h : ℝ → ℝ) (R : ℝ) := Lp ℂ 2 (muG h R) × Lp ℂ 2 (muB R) × Hm12

/-- Remark 2.9, p. 14: `L²(Γ_R) × L²(∂B_R^-)` (product norm: the maximum of the two norms). -/
abbrev Ysp (h : ℝ → ℝ) (R : ℝ) := Lp ℂ 2 (muG h R) × Lp ℂ 2 (muB R)

/-- Eqs. (2.4)-(2.7), pp. 5-6: `∫_{Γ_R} K(y) φ₁(y) ds(y) + ∫_{∂B_R^-} K(y) φ₂(y) ds(y)`. -/
def bdryPair (h : ℝ → ℝ) (R : ℝ) (K : R2 → ℂ) (φ1 φ2 : ℝ → ℂ) : ℂ :=
  (∫ t, K (gPt h t) * φ1 t ∂(muG h R)) + ∫ θ, K (cPt R θ) * φ2 θ ∂(muB R)

/-- Eqs. (2.4)-(2.7), pp. 5-6: `∫_{Γ̃} K(y) φ₃(y) ds(y) = ∑_n a_n ∫_0^{2π} K(z(s)) e^{ins} ds`,
where `a_n` are the Fourier coefficients of `s ↦ φ₃(z(s)) |z'(s)|`. -/
def auxPair (z : ℝ → R2) (K : R2 → ℂ) (a : ℤ → ℂ) : ℂ :=
  ∑' n : ℤ, a n * ∫ s in (0 : ℝ)..(2 * Real.pi),
    K (z s) * Complex.exp (Complex.I * (n : ℂ) * (s : ℂ))

/-- Eq. (2.10), p. 6: the single-layer potential
`(𝒮_{k,Γ_R} φ₁)(x) + (𝒮_{k,∂B_R^-} φ₂)(x) = ∫_{Γ_R} Φ_k(x,y) φ₁ ds + ∫_{∂B_R^-} Φ_k(x,y) φ₂ ds`;
it is also the field (2.34) of Remark 2.9. -/
def slPotB (k : ℝ) (h : ℝ → ℝ) (R : ℝ) (φ1 φ2 : ℝ → ℂ) (x : R2) : ℂ :=
  bdryPair h R (fun y => Phi k x y) φ1 φ2

/-- Eq. (2.10), p. 6: the scattered field
`u^s = 𝒮_{k,Γ_R} φ₁ + 𝒮_{k,∂B_R^-} φ₂ + 𝒮_{k,Γ̃} φ₃`, `φ₃` given by its coefficients `a`. -/
def slPot (k : ℝ) (h : ℝ → ℝ) (R : ℝ) (z : ℝ → R2) (φ1 φ2 : ℝ → ℂ) (a : ℤ → ℂ) (x : R2) : ℂ :=
  slPotB k h R φ1 φ2 x + auxPair z (fun y => Phi k x y) a

/-- Eq. (2.5), p. 5: the constant `e^{iπ/4}/√(8πk)` of the far-field patterns (it is `γ` of
Lemma 4.2, p. 19). -/
def gammaInf (k : ℝ) : ℂ :=
  Complex.exp (Complex.I * (Real.pi : ℂ) / 4) / (Real.sqrt (8 * Real.pi * k) : ℂ)

/-- Eqs. (2.5) and (2.36), pp. 5, 14: `(S^∞_{k,Γ_R} φ₁)(x̂) + (S^∞_{k,∂B_R^-} φ₂)(x̂)` with
`(S^∞_{k,I} φ)(x̂) = e^{iπ/4}/√(8πk) ∫_I e^{-ik x̂ · y} φ(y) ds(y)`. -/
def ffPotB (k : ℝ) (h : ℝ → ℝ) (R : ℝ) (φ1 φ2 : ℝ → ℂ) (xhat : R2) : ℂ :=
  gammaInf k * bdryPair h R (fun y => Complex.exp (-(Complex.I * (k : ℂ) * (dot xhat y : ℂ))))
    φ1 φ2

/-- Eq. (2.33), p. 14: `u^∞ = S^∞Φ = S^∞_{k,Γ_R} φ₁ + S^∞_{k,∂B_R^-} φ₂ + S^∞_{k,Γ̃} φ₃`. -/
def ffPot (k : ℝ) (h : ℝ → ℝ) (R : ℝ) (z : ℝ → R2) (φ1 φ2 : ℝ → ℂ) (a : ℤ → ℂ)
    (xhat : R2) : ℂ :=
  ffPotB k h R φ1 φ2 xhat +
    gammaInf k * auxPair z (fun y => Complex.exp (-(Complex.I * (k : ℂ) * (dot xhat y : ℂ)))) a

/-! ### The operators `A`, `B` and the right-hand side `G` (eqs. (2.14)-(2.16), (2.35)) -/

/-- Eq. (2.15), p. 7: the kernel `y ↦ ∂Φ_k(x,y)/∂ν(x)` at `x = (t, h(t)) ∈ Γ_R` (first row of
`A`: `K'_{k, I_p → Γ_R}`). -/
def kerG (k : ℝ) (h : ℝ → ℝ) (t : ℝ) (y : R2) : ℂ := dPhi k (gPt h t) (gNormal h t) y

/-- Eq. (2.15), p. 7: the kernel `y ↦ ∂Φ_k(x,y)/∂ν(x) - ∂Φ_k(x^{re},y)/∂ν(x^{re})` at
`x = R(cos θ, sin θ) ∈ ∂B_R^-`, `ν(x^{re}) = x^{re}/R` (second row of `A`:
`K'_{k, I_p → ∂B_R^-} - K'^{,re}_{k, I_p → ∂B_R^-}`). -/
def kerB (k : ℝ) (R : ℝ) (θ : ℝ) (y : R2) : ℂ :=
  dPhi k (cPt R θ) (cNormal θ) y - dPhi k (refl (cPt R θ)) (refl (cNormal θ)) y

/-- Eq. (2.15), p. 7: the kernel `y ↦ ∂Φ_k(x,y)/∂ν(x) + iρ Φ_k(x,y)` at `x = z(s) ∈ Γ̃`, `ν` the
normal pointing out of `D̃` (third row of `A`: `K'_{k, I_p → Γ̃} + iρ S_{k, I_p → Γ̃}`). -/
def kerT (k ρ : ℝ) (z : ℝ → R2) (s : ℝ) (y : R2) : ℂ :=
  dPhi k (z s) (auxNormal z s) y + Complex.I * (ρ : ℂ) * Phi k (z s) y

/-- Eq. (2.15), p. 7, and eq. (2.35), p. 14: the first row of `B`,
`(B Φ)₁ = -2 K'_{k,Γ_R→Γ_R} φ₁ - 2 K'_{k,∂B_R^-→Γ_R} φ₂`, at `(t, h(t)) ∈ Γ_R`. -/
def opB1 (k : ℝ) (h : ℝ → ℝ) (R : ℝ) (φ1 φ2 : ℝ → ℂ) (t : ℝ) : ℂ :=
  -2 * bdryPair h R (kerG k h t) φ1 φ2

/-- Eq. (2.15), p. 7, and eq. (2.35), p. 14: the second row of `B`,
`(B Φ)₂ = -2 (K' - K'^{,re})_{k,Γ_R→∂B_R^-} φ₁ - 2 (K' - K'^{,re})_{k,∂B_R^-→∂B_R^-} φ₂`, at
`R(cos θ, sin θ) ∈ ∂B_R^-`. -/
def opB2 (k : ℝ) (h : ℝ → ℝ) (R : ℝ) (φ1 φ2 : ℝ → ℂ) (θ : ℝ) : ℂ :=
  -2 * bdryPair h R (kerB k R θ) φ1 φ2

/-- Eq. (2.15), p. 7: the first row of `A`, `(AΦ)₁ = A₁₁φ₁ + A₁₂φ₂ + A₁₃φ₃` on `Γ_R`. -/
def opA1 (k : ℝ) (h : ℝ → ℝ) (R : ℝ) (z : ℝ → R2) (φ1 φ2 : ℝ → ℂ) (a : ℤ → ℂ) (t : ℝ) : ℂ :=
  opB1 k h R φ1 φ2 t + -2 * auxPair z (kerG k h t) a

/-- Eq. (2.15), p. 7: the second row of `A`, `(AΦ)₂ = A₂₁φ₁ + A₂₂φ₂ + A₂₃φ₃` on `∂B_R^-`. -/
def opA2 (k : ℝ) (h : ℝ → ℝ) (R : ℝ) (z : ℝ → R2) (φ1 φ2 : ℝ → ℂ) (a : ℤ → ℂ) (θ : ℝ) : ℂ :=
  opB2 k h R φ1 φ2 θ + -2 * auxPair z (kerB k R θ) a

/-- The weight `e^{-ims} |z'(s)| / (2π)` that turns a function `F` on `Γ̃` into the `m`-th
Fourier coefficient `(1/2π) ∫_0^{2π} F(z(s)) |z'(s)| e^{-ims} ds` of `s ↦ F(z(s)) |z'(s)|`. -/
def fourierWeight (z : ℝ → R2) (m : ℤ) (s : ℝ) : ℂ :=
  Complex.exp (-(Complex.I * (m : ℂ) * (s : ℂ))) * (‖deriv z s‖ : ℂ) / (2 * Real.pi : ℂ)

/-- Eq. (2.15), p. 7: the third row of `A`, `(AΦ)₃ = A₃₁φ₁ + A₃₂φ₂ + A₃₃φ₃ ∈ H^{-1/2}(Γ̃)`, given
by its `m`-th Fourier coefficient (in the representation of `Hm12`). The term `A₃₃φ₃`, with
`A₃₃ = -2(K'_{k,Γ̃→Γ̃} + iρ S_{k,Γ̃→Γ̃})` acting on `H^{-1/2}(Γ̃)`, is the matrix
`∑_n a_n (1/2π) ∫_0^{2π} ∫_0^{2π} e^{-ims} |z'(s)| (∂Φ_k(z(s),z(t))/∂ν(z(s)) + iρ Φ_k(z(s),z(t)))
e^{int} dt ds`. -/
def opA3 (k ρ : ℝ) (h : ℝ → ℝ) (R : ℝ) (z : ℝ → R2) (φ1 φ2 : ℝ → ℂ) (a : ℤ → ℂ) (m : ℤ) : ℂ :=
  -2 * ((∫ s in (0 : ℝ)..(2 * Real.pi), fourierWeight z m s * bdryPair h R (kerT k ρ z s) φ1 φ2) +
    ∑' n : ℤ, a n * ∫ s in (0 : ℝ)..(2 * Real.pi), fourierWeight z m s *
      ∫ t in (0 : ℝ)..(2 * Real.pi), kerT k ρ z s (z t) * Complex.exp (Complex.I * (n : ℂ) * (t : ℂ)))

/-- Eq. (2.16), p. 7: the first component `2(∂u^i/∂ν + ∂u^r/∂ν)` of `G`, on `Γ_R`, at
`(t, h(t))`. -/
def gData (k : ℝ) (d : R2) (h : ℝ → ℝ) (t : ℝ) : ℂ := -2 * incData k d h t

/-- Eq. (2.14), p. 7: `Φ = (φ₁, φ₂, φ₃) ∈ X` solves `(I + A)Φ = G` with `A` of (2.15), `ρ` the
impedance constant of (2.13), and `G = (2(∂u^i/∂ν + ∂u^r/∂ν)|_{Γ_R}, 0, 0)` of (2.16). -/
def IsBIESolution (k ρ : ℝ) (h : ℝ → ℝ) (R : ℝ) (aux : AuxDomain h R) (d : R2)
    (sol : Xsp h R) : Prop :=
  (∀ᵐ t ∂(muG h R),
    sol.1 t + opA1 k h R aux.z ⇑sol.1 ⇑sol.2.1 (hmhCoeff sol.2.2) t = gData k d h t) ∧
  (∀ᵐ θ ∂(muB R), sol.2.1 θ + opA2 k h R aux.z ⇑sol.1 ⇑sol.2.1 (hmhCoeff sol.2.2) θ = 0) ∧
  ∀ m : ℤ, hmhCoeff sol.2.2 m + opA3 k ρ h R aux.z ⇑sol.1 ⇑sol.2.1 (hmhCoeff sol.2.2) m = 0

/-- Eq. (2.35), p. 14: `Ψ = (φ₁, φ₂) ∈ L²(Γ_R) × L²(∂B_R^-)` solves `(I + B)Ψ = (g₁, g₂)`. -/
def IsBSolution (k : ℝ) (h : ℝ → ℝ) (R : ℝ) (psi : Ysp h R) (g1 g2 : ℝ → ℂ) : Prop :=
  (∀ᵐ t ∂(muG h R), psi.1 t + opB1 k h R ⇑psi.1 ⇑psi.2 t = g1 t) ∧
  (∀ᵐ θ ∂(muB R), psi.2 θ + opB2 k h R ⇑psi.1 ⇑psi.2 θ = g2 θ)

/-- Section 3.1, eq. (3.1), p. 15: both `x` and `y` lie within distance `r` of the same corner
(`x_A` or `x_B`) of `∂D_R^-`. -/
def NearSameCorner (R r : ℝ) (x y : R2) : Prop :=
  (dist x (xA R) < r ∧ dist y (xA R) < r) ∨ (dist x (xB R) < r ∧ dist y (xB R) < r)

open Classical in
/-- Section 3.1, eq. (3.1), p. 15: the first row of `Â⋆₁₁`, the part of `Â₁₁ = B` whose kernel
is that of `B` when `x` and `y` are within distance `r` of the same corner and `0` otherwise. -/
def opBstar1 (k : ℝ) (h : ℝ → ℝ) (R r : ℝ) (φ1 φ2 : ℝ → ℂ) (t : ℝ) : ℂ :=
  -2 * bdryPair h R (fun y => if NearSameCorner R r (gPt h t) y then kerG k h t y else 0) φ1 φ2

open Classical in
/-- Section 3.1, eq. (3.1), p. 15: the second row of `Â⋆₁₁` (see `opBstar1`). -/
def opBstar2 (k : ℝ) (h : ℝ → ℝ) (R r : ℝ) (φ1 φ2 : ℝ → ℂ) (θ : ℝ) : ℂ :=
  -2 * bdryPair h R (fun y => if NearSameCorner R r (cPt R θ) y then kerB k R θ y else 0) φ1 φ2

/-! ### The inverse problem (Section 4, pp. 18-20) -/

/-- Lemma 4.1, p. 18: the exterior `ℝ²_+ \ \overline{B_R} = {x : x₂ > 0, |x| > R}` of the disc in
the upper half-plane. -/
def upperExt (R : ℝ) : Set R2 := {x | 0 < x 1 ∧ R < ‖x‖}

/-- Lemma 4.1, p. 18: the Neumann condition `∂u/∂ν = 0` on the flat part
`{(x₁, 0) : |x₁| > R}` of the boundary of `ℝ²_+ \ \overline{B_R}`, in weak form:
`∫_{ℝ²_+ \ \overline{B_R}} (∇u · ∇φ - k² u φ) dx = 0` for every `φ ∈ C_c^∞(ℝ²)` whose support
does not meet `\overline{B_R}`. -/
def IsFlatNeumannWeak (k R : ℝ) (u : R2 → ℂ) : Prop :=
  ∀ φ : R2 → ℂ, IsTestFn φ → tsupport φ ⊆ {x | R < ‖x‖} →
    ∫ x in upperExt R, (gradDot u φ x - (k : ℂ) ^ 2 * u x * φ x) = 0

/-- Section 4, p. 19: the Neumann data `f(·;y) = -(∂u^i(·;y)/∂ν + ∂u^r(·;y)/∂ν)` at `(t, h(t))`
for the point source `u^i(x;y) = Φ_k(x,y)` and its reflection `u^r(x;y) = Φ_k(x,y^{re})`. -/
def pointData (k : ℝ) (h : ℝ → ℝ) (y : R2) (t : ℝ) : ℂ :=
  -(fderiv ℝ (fun x => Phi k x y + Phi k x (refl y)) (gPt h t) (gNormal h t))

/-! ### The spline basis (Remark 5.2, p. 22) -/

/-- Remark 5.2, p. 22: the truncated power `z_+^m = z^m` for `z ≥ 0` and `0` for `z < 0`. -/
def truncPow (m : ℕ) (z : ℝ) : ℝ := if 0 ≤ z then z ^ m else 0

/-- Remark 5.2, p. 22: `φ(t) = ∑_{j=0}^{m+1} (-1)^j/m! · C(m+1, j) · (t + (m+1)/2 - j)_+^m`
(the paper writes `k` for the degree `m` and chooses `k = 4`). -/
def splinePhi (m : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 2), (-1 : ℝ) ^ j / (m.factorial : ℝ) * ((m + 1).choose j : ℝ) *
    truncPow m (t + ((m : ℝ) + 1) / 2 - j)

/-- Remark 5.2, p. 22: the mesh width `h = 2R/(M + 5)`. -/
def splineStep (R : ℝ) (M : ℕ) : ℝ := 2 * R / ((M : ℝ) + 5)

/-- Remark 5.2, p. 22: the knots `t_i = (i + 2)h - R`. -/
def splineKnot (R : ℝ) (M i : ℕ) : ℝ := ((i : ℝ) + 2) * splineStep R M - R

/-- Remark 5.2, p. 22: the basis function `φ_{i,M}(t) = φ((t - t_i)/h)` of `R_M`, with
`k = 4`. -/
def splineBasis (R : ℝ) (M i : ℕ) (t : ℝ) : ℝ :=
  splinePhi 4 ((t - splineKnot R M i) / splineStep R M)

end Arxiv1901_08703


