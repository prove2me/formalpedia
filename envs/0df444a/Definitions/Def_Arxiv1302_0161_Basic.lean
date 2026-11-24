-- Prove2me | Definitions.Def_Arxiv1302_0161_Basic
-- name    : Arxiv1302_0161_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T09:23:00.136806+00:00
-- url     : https://prove2.me/theorems/356c6376-0693-411e-82c7-27803fed804b
-- title:
--   Locally rough surface scattering: Dirichlet problem, layer potentials and the integral equation $P\varphi=g$
-- statement:
--   Objects of Sections 1–5 of H. Zhang and B. Zhang (arXiv:1302.0161).
--
--   1. **Surface and waves.** A locally rough surface is $\Gamma=\{x_2=h_\Gamma(x_1)\}$ with $h_\Gamma\in C^2(\mathbb R)$ of compact support. Above it lies $D_+=\{x_2>h_\Gamma(x_1)\}$, with closure $\overline{D_+}=\{x_2\ge h_\Gamma(x_1)\}$. The wave number is $k>0$. An incident direction is $d\in S_-=\{|d|=1,\ d_2<0\}$. The incident wave is $u^i(x)=e^{ikd\cdot x}$ and the reflected wave is $u^r(x)=-e^{ik(d_1x_1-d_2x_2)}$. Write $S_+=\{|x|=1,\ x_2>0\}$.
--   2. **Fundamental solution.** $\Phi_k(x,y)=\tfrac i4H_0^{(1)}(k|x-y|)$, where $H_0^{(1)}=J_0+iY_0$. Both $J_0$ and $Y_0$ are given by their power series, $Y_0$ with the term $\tfrac2\pi(\ln\tfrac r2+\gamma)J_0(r)$. The normal derivative is $\partial\Phi_k(x,y)/\partial\nu(y)=\nabla_y\Phi_k(x,y)\cdot\nu$.
--   3. **Dirichlet problem (DP).** $u$ solves (DP) with data $f$ if all of the following hold:
--      - $u\in C^2(D_+)\cap C(\overline{D_+})$;
--      - $\Delta u+k^2u=0$ in $D_+$;
--      - $|x|^{1/2}(\partial_ru-iku)\to0$ as $|x|\to\infty$ in $D_+$;
--      - $u=f$ on $\Gamma$.
--
--      The scattering problem takes $f=-(u^i+u^r)$. A function $F$ is the far field pattern of $u$ on a set $A$ of directions if $u(x)=\frac{e^{ik|x|}}{\sqrt{|x|}}\big(F(\hat x)+O(|x|^{-1})\big)$ uniformly for $\hat x=x/|x|\in A$.
--   4. **The bounded curve.** $R>0$ is chosen so that $\Gamma_p=\{(x_1,h_\Gamma(x_1)):x_1\in\operatorname{supp}h_\Gamma\}\subset B_R$. Then:
--      - $\Gamma_R=\{(t,h_\Gamma(t)):-R<t<R\}$;
--      - $\partial D_R^-=\overline{\Gamma_R}\cup\{|x|=R,\ x_2\le0\}$, with corners $x_A=(-R,0)$ and $x_B=(R,0)$;
--      - $\overline{D_R^-}=\{x_2\le h_\Gamma(x_1),\ |x|\le R\}$.
--
--      Integrals over $\partial D_R^-$ are taken with respect to arc length, and $\nu$ is the unit normal pointing out of $D_R^-$.
--   5. **Layer potentials and the equation (2.2)–(2.4).** The potentials are $\mathcal S_k\varphi(x)=\int\Phi_k(x,y)\varphi(y)\,ds(y)$ and $\mathcal D_k\varphi(x)=\int\partial_{\nu(y)}\Phi_k(x,y)\varphi(y)\,ds(y)$. On the curve the same integrals are $S_k\varphi$ and $K_k\varphi$; evaluated at $x^{re}=(x_1,-x_2)$ they are $S_k^{re}\varphi$ and $K_k^{re}\varphi$. Let $\psi^{re}(x)=x$ on $\Gamma_R$ and $\psi^{re}(x)=x^{re}$ elsewhere on the curve. For real $\eta\neq0$:
--      - $P\varphi(x)=c(x)\varphi(x)+(\mathcal D_k-i\eta\mathcal S_k)\varphi(x)+(\mathcal D_k-i\eta\mathcal S_k)\varphi(\psi^{re}(x))$, where $c=1$ on $\Gamma_R$ and $c=\tfrac12$ on the semicircle and the corners;
--      - $g=-2(u^i+u^r)$ on $\Gamma_R$ and $g=0$ elsewhere on the curve.
--
--      The far-field formula (2.8) is $u^\infty(\hat x)=\frac{e^{-i\pi/4}}{\sqrt{8\pi k}}\int[k\nu(y)\cdot\hat x+\eta]e^{-ik\hat x\cdot y}\varphi(y)\,ds(y)$.
--   6. **Graded mesh (Section 3).** Let $v(s)=(\tfrac1p-\tfrac12)(\tfrac{\pi-2s}{\pi})^3+\tfrac1p\tfrac{2s-\pi}{\pi}+\tfrac12$. The grading function is $\omega(s)=\pi v(s)^p/(v(s)^p+v(\pi-s)^p)$ on $[0,\pi]$ and $\omega(s)=\omega(s-\pi)+\pi$ on $(\pi,2\pi]$. The parameterisation, with $p=4$, is:
--      - $x(s)=(-2R\omega(s)/\pi+R,\ h_\Gamma(-2R\omega(s)/\pi+R))$ for $0\le s\le\pi$;
--      - $x(s)=R(\cos\omega(s),\sin\omega(s))$ for $\pi<s\le2\pi$.
--
--      It comes with its outward normal $\nu(x(s))$ and its speed $|x'(s)|$.
--   7. **Section 4.**
--      - $C^2_{0,R}(\mathbb R)=\{h\in C^2:\operatorname{supp}h\subset(-R,R)\}$, with $\|h\|_{C^2}=\sup|h|+\sup|h'|+\sup|h''|$.
--      - $\|F\|_{L^2(S_+)}^2=\int_0^\pi|F(\cos\theta,\sin\theta)|^2d\theta$.
--      - The boundary data of the derivative is $-(\nu_2\Delta h)\,\partial u/\partial\nu$ on $\Gamma$. Here $\nu=(-h_\Gamma',1)/\sqrt{1+h_\Gamma'^2}$ points into $D_+$, and $\partial u/\partial\nu$ is the one-sided derivative from $D_+$.
--   8. **Splines (Remark 5.1).** $\phi(t)=\sum_{j=0}^{m+1}\frac{(-1)^j}{m!}\binom{m+1}{j}(t+\frac{m+1}2-j)_+^m$ with $m=4$. Let $h=2R/(M+5)$ and $t_i=(i+2)h-R$. Then $\phi_i(t)=\phi((t-t_i)/h)$.
--
--   **Formalization Note** Points of $\mathbb R^2$ are elements of `EuclideanSpace ℝ (Fin 2)`. A function on $\partial D_R^-$ is a function on $\mathbb R^2$ of which only the values on the curve are used. Arc-length integrals over $\partial D_R^-$ are written in the natural parameterisations: $t\mapsto(t,h_\Gamma(t))$, $-R\le t\le R$, and $\theta\mapsto R(\cos\theta,\sin\theta)$, $\pi\le\theta\le2\pi$. The operator $P$, the potentials and $g$ are total functions on $\mathbb R^2$; the statements use them only on $\partial D_R^-$. The paper's spline degree $k$ is called $m$, to avoid a clash with the wave number.
-- source:
--   H. Zhang and B. Zhang, A novel integral equation for scattering by locally rough surfaces and application to the inverse problem, arXiv:1302.0161v1 (2013), Sections 1-2 (pp. 2-9, eqs. (1.1)-(1.3), (2.1)-(2.4), (2.8)), Section 3 (pp. 9-10), Section 4 (pp. 10-11), Remark 5.1 (p. 12)

import Mathlib

/-!
H. Zhang and B. Zhang, *A novel integral equation for scattering by locally rough surfaces and
application to the inverse problem*, arXiv:1302.0161v1 (2013): the locally rough surface, the
incident and reflected plane waves, the Dirichlet problem (DP) and the far field pattern of
Section 1 and Section 2; the layer potentials, the operator `P` and the right-hand side `g` of
eqs. (2.2)-(2.4); the far-field formula (2.8); the graded-mesh parameterisation of Section 3;
the far field data, the space `C²_{0,R}(ℝ)` and the boundary data of the domain derivative of
Section 4; and the spline basis of Remark 5.1.

Points of `ℝ²` are elements of `EuclideanSpace ℝ (Fin 2)`; the paper's `x = (x₁, x₂)` is
`x 0 = x₁`, `x 1 = x₂`. A function on the curve `∂D_R^-` is a function on `ℝ²` of which only the
values on the curve are used. Integrals over the curve are line integrals with respect to arc
length, written in the natural parameterisations: `t ↦ (t, h t)`, `-R ≤ t ≤ R`, for `Γ_R`, and
`θ ↦ R (cos θ, sin θ)`, `π ≤ θ ≤ 2π`, for the lower semicircle.
-/

open MeasureTheory

noncomputable section

namespace Arxiv1302_0161

/-- The plane `ℝ²` with its Euclidean norm. -/
abbrev R2 := EuclideanSpace ℝ (Fin 2)

/-- The point `(a, b) ∈ ℝ²`. -/
def pt (a b : ℝ) : R2 := !₂[a, b]

/-- The Euclidean inner product `x · y = x₁ y₁ + x₂ y₂` of `ℝ²`. -/
def dot (x y : R2) : ℝ := x 0 * y 0 + x 1 * y 1

/-- Section 2, p. 5: the reflection `x^{re} = (x₁, -x₂)` of `x` about the `x₁`-axis. -/
def refl (x : R2) : R2 := pt (x 0) (-(x 1))

/-! ### The fundamental solution (Section 2, p. 5) -/

/-- The Bessel function `J₀(r) = ∑_{m ≥ 0} (-1)^m (r/2)^{2m} / (m!)²` (Section 2, p. 5, through
`Φ_k`; Section 3, p. 10). -/
def besselJ0 (r : ℝ) : ℝ :=
  ∑' m : ℕ, (-1 : ℝ) ^ m * (r / 2) ^ (2 * m) / ((m.factorial : ℝ) ^ 2)

/-- The Bessel function of the second kind of order zero, for `r > 0`:
`Y₀(r) = (2/π)(log(r/2) + γ) J₀(r) + (2/π) ∑_{m ≥ 1} (-1)^{m+1} H_m (r/2)^{2m} / (m!)²`,
with `H_m` the harmonic numbers and `γ` the Euler–Mascheroni constant. -/
def besselY0 (r : ℝ) : ℝ :=
  2 / Real.pi * (Real.log (r / 2) + Real.eulerMascheroniConstant) * besselJ0 r +
    2 / Real.pi * ∑' m : ℕ, (-1 : ℝ) ^ m * (harmonic (m + 1) : ℝ) * (r / 2) ^ (2 * (m + 1)) /
      (((m + 1).factorial : ℝ) ^ 2)

/-- The Hankel function of the first kind of order zero, `H₀^{(1)} = J₀ + i Y₀`, for `r > 0`. -/
def hankel01 (r : ℝ) : ℂ := (besselJ0 r : ℂ) + Complex.I * (besselY0 r : ℂ)

/-- Section 2, p. 5: the fundamental solution `Φ_k(x,y) = (i/4) H₀^{(1)}(k|x-y|)` of the
Helmholtz equation `Δw + k²w = 0`, for `k > 0` and `x ≠ y`. -/
def Phi (k : ℝ) (x y : R2) : ℂ := Complex.I / 4 * hankel01 (k * ‖x - y‖)

/-- Section 2, p. 5: the normal derivative `∂Φ_k(x,y)/∂ν(y) = ∇_y Φ_k(x,y) · ν` in the direction
of a normal vector `ν` at `y`. -/
def dPhi (k : ℝ) (x y nu : R2) : ℂ := fderiv ℝ (fun z => Phi k x z) y nu

/-! ### The locally rough surface and the Dirichlet problem (Sections 1 and 2, pp. 2-5) -/

/-- Section 1, p. 2: `h_Γ ∈ C²(ℝ)` has compact support; `Γ = {x₂ = h_Γ(x₁)}` is a locally rough
surface. -/
def IsLocalProfile (h : ℝ → ℝ) : Prop := ContDiff ℝ 2 h ∧ HasCompactSupport h

/-- Section 1, p. 2: `D_+ = {(x₁, x₂) : x₂ > h_Γ(x₁)}`. -/
def Dplus (h : ℝ → ℝ) : Set R2 := {x | h (x 0) < x 1}

/-- The closure `\overline{D_+} = {(x₁, x₂) : x₂ ≥ h_Γ(x₁)}` (Section 2, p. 4). -/
def DplusClosed (h : ℝ → ℝ) : Set R2 := {x | h (x 0) ≤ x 1}

/-- Section 1, p. 2: the surface `Γ = ∂D_+ = {(x₁, x₂) : x₂ = h_Γ(x₁)}`. -/
def Gam (h : ℝ → ℝ) : Set R2 := {x | x 1 = h (x 0)}

/-- Section 1, p. 2: `d ∈ S_- = {x : |x| = 1, x₂ < 0}`, an incident direction. -/
def IsLowerDir (d : R2) : Prop := ‖d‖ = 1 ∧ d 1 < 0

/-- Section 1, p. 2: the upper half `S_+ = {x : |x| = 1, x₂ > 0}` of the unit circle. -/
def upperCircle : Set R2 := {x | ‖x‖ = 1 ∧ 0 < x 1}

/-- Section 1, p. 2: the incident plane wave `u^i(x) = exp(i k d · x)`. -/
def uInc (k : ℝ) (d x : R2) : ℂ := Complex.exp (Complex.I * (k : ℂ) * (dot d x : ℂ))

/-- Section 1, p. 2: the wave reflected by the plane `x₂ = 0`,
`u^r(x) = -exp(i k (x₁ sin θ + x₂ cos θ))` for `d = (sin θ, -cos θ)`, that is
`u^r(x) = -exp(i k (d₁ x₁ - d₂ x₂))`. -/
def uRefl (k : ℝ) (d x : R2) : ℂ :=
  -Complex.exp (Complex.I * (k : ℂ) * ((d 0 * x 0 - d 1 * x 1 : ℝ) : ℂ))

/-- Section 2, p. 4: the boundary data `f = -(u^i + u^r)` of the scattering problem. -/
def incData (k : ℝ) (d x : R2) : ℂ := -(uInc k d x + uRefl k d x)

/-- Eq. (1.3), p. 2: the Sommerfeld radiation condition
`lim_{r → ∞} r^{1/2} (∂u/∂r - i k u) = 0`, `r = |x|`, `x ∈ D`, with `∂u/∂r = ∇u(x) · x/|x|`;
the limit is taken as `|x| → ∞` within `D`. -/
def IsRadiating (k : ℝ) (D : Set R2) (u : R2 → ℂ) : Prop :=
  ∀ ε > 0, ∃ ρ : ℝ, ∀ x ∈ D, ρ < ‖x‖ →
    ‖(Real.sqrt ‖x‖ : ℂ) * (fderiv ℝ u x (‖x‖⁻¹ • x) - Complex.I * (k : ℂ) * u x)‖ < ε

/-- Section 2, p. 4: `u` solves the Dirichlet problem (DP) with boundary data `f`:
`u ∈ C²(D_+) ∩ C(\overline{D_+})`, `Δu + k²u = 0` in `D_+` (eq. (1.1)), `u` satisfies the
Sommerfeld radiation condition (1.3), and `u = f` on `Γ` (eq. (2.1)). -/
def IsDPSolution (k : ℝ) (h : ℝ → ℝ) (f : R2 → ℂ) (u : R2 → ℂ) : Prop :=
  ContDiffOn ℝ 2 u (Dplus h) ∧ ContinuousOn u (DplusClosed h) ∧
    (∀ x ∈ Dplus h, Laplacian.laplacian u x + (k : ℂ) ^ 2 * u x = 0) ∧
    IsRadiating k (Dplus h) u ∧ ∀ x ∈ Gam h, u x = f x

/-- Section 1, p. 2 and Remark 2.6, p. 9: `F` is the far field pattern of `u` for the
observation directions in `A`: `u(x) = e^{ik|x|}/√|x| (F(x̂) + O(1/|x|))` as `|x| → ∞`,
uniformly for `x̂ = x/|x| ∈ A`. -/
def HasFarFieldOn (k : ℝ) (u : R2 → ℂ) (F : R2 → ℂ) (A : Set R2) : Prop :=
  ∃ C ρ : ℝ, 0 < ρ ∧ ∀ x : R2, ρ ≤ ‖x‖ → ‖x‖⁻¹ • x ∈ A →
    ‖u x - Complex.exp (Complex.I * (k : ℂ) * (‖x‖ : ℂ)) / (Real.sqrt ‖x‖ : ℂ) * F (‖x‖⁻¹ • x)‖ ≤
      C / (‖x‖ * Real.sqrt ‖x‖)

/-! ### The bounded curve `∂D_R^-` and the integral equation (Section 2, pp. 4-6) -/

/-- Section 2, p. 4: `R > 0` and the local perturbation
`Γ_p = {(x₁, h_Γ(x₁)) : x₁ ∈ supp(h_Γ)}` lies in the open disc `B_R = {|x| < R}`. -/
def PerturbationInBall (h : ℝ → ℝ) (R : ℝ) : Prop :=
  0 < R ∧ ∀ t ∈ tsupport h, t ^ 2 + h t ^ 2 < R ^ 2

/-- Section 2, p. 4: `Γ_R = Γ ∩ B_R = {(x₁, h_Γ(x₁)) : -R < x₁ < R}` (when `Γ_p ⊂ B_R`). -/
def gammaR (h : ℝ → ℝ) (R : ℝ) : Set R2 := {x | -R < x 0 ∧ x 0 < R ∧ x 1 = h (x 0)}

/-- Section 2, p. 4: the closed curve `∂D_R^- = Γ_R ∪ ∂B_R^- ∪ {x_A, x_B}`, the boundary of
`D_R^- = B_R ∩ D_-`, with corners `x_A = (-R, 0)`, `x_B = (R, 0)`. -/
def bdry (h : ℝ → ℝ) (R : ℝ) : Set R2 :=
  {x | -R ≤ x 0 ∧ x 0 ≤ R ∧ x 1 = h (x 0)} ∪ {x | ‖x‖ = R ∧ x 1 ≤ 0}

/-- The closure `\overline{D_R^-} = {x : x₂ ≤ h_Γ(x₁), |x| ≤ R}` of `D_R^-` (Section 2, p. 4). -/
def lowerClosed (h : ℝ → ℝ) (R : ℝ) : Set R2 := {x | x 1 ≤ h (x 0) ∧ ‖x‖ ≤ R}

/-- The unit normal to `Γ` at `(t, h_Γ(t))` pointing into `D_+`,
`ν = (-h_Γ'(t), 1)/√(1 + h_Γ'(t)²)`. On `Γ_R` it is the normal of `∂D_R^-` pointing out of
`D_R^-` (Section 2, p. 5), and it is the normal of Theorem 4.2 (p. 11). -/
def gNormal (h : ℝ → ℝ) (t : ℝ) : R2 := (Real.sqrt (1 + deriv h t ^ 2))⁻¹ • pt (-deriv h t) 1

/-- The line integral `∫_{∂D_R^-} F(y, ν(y)) ds(y)` with respect to arc length, `ν` the unit normal
pointing out of `D_R^-`: over `Γ_R` as `∫_{-R}^{R} F((t, h t), ν) √(1 + h'(t)²) dt`, and over the
lower semicircle as `∫_π^{2π} F(R(cos θ, sin θ), (cos θ, sin θ)) R dθ` (Section 2, p. 5). -/
def bdryInt (h : ℝ → ℝ) (R : ℝ) (F : R2 → R2 → ℂ) : ℂ :=
  (∫ t in (-R)..R, F (pt t (h t)) (gNormal h t) * (Real.sqrt (1 + deriv h t ^ 2) : ℂ)) +
    ∫ θ in Real.pi..(2 * Real.pi),
      F (pt (R * Real.cos θ) (R * Real.sin θ)) (pt (Real.cos θ) (Real.sin θ)) * (R : ℂ)

/-- Section 2, p. 5: the single-layer potential `(𝒮_k φ)(x) = ∫_{∂D_R^-} Φ_k(x,y) φ(y) ds(y)`;
for `x ∈ ∂D_R^-` this is the boundary operator `(S_k φ)(x)`, and at `x^{re}` it gives
`(S_k^{re} φ)(x)`. -/
def singleLayer (k : ℝ) (h : ℝ → ℝ) (R : ℝ) (phi : R2 → ℂ) (x : R2) : ℂ :=
  bdryInt h R (fun y _ => Phi k x y * phi y)

/-- Section 2, p. 5: the double-layer potential
`(𝒟_k φ)(x) = ∫_{∂D_R^-} ∂Φ_k(x,y)/∂ν(y) φ(y) ds(y)`, `ν` the unit normal pointing out of `D_R^-`;
for `x ∈ ∂D_R^-` this is the boundary operator `(K_k φ)(x)`, and at `x^{re}` it gives
`(K_k^{re} φ)(x)`. -/
def doubleLayer (k : ℝ) (h : ℝ → ℝ) (R : ℝ) (phi : R2 → ℂ) (x : R2) : ℂ :=
  bdryInt h R (fun y nu => dPhi k x y nu * phi y)

/-- Eq. (2.2), p. 5: the combined layer potential `u^s = 𝒟_k φ - i η 𝒮_k φ`, `η` the real coupling
parameter; on `∂D_R^-` it is `K_k φ - i η S_k φ`. -/
def combinedPot (k eta : ℝ) (h : ℝ → ℝ) (R : ℝ) (phi : R2 → ℂ) (x : R2) : ℂ :=
  doubleLayer k h R phi x - Complex.I * (eta : ℂ) * singleLayer k h R phi x

open Classical in
/-- Section 2, p. 5: the map `ψ^{re} : ∂D_R^- → ∂D_R^+`, `ψ^{re}(x) = x` on `Γ_R` and
`ψ^{re}(x) = x^{re}` on `∂B_R^- ∪ {x_A, x_B}`. -/
def psiRe (h : ℝ → ℝ) (R : ℝ) (x : R2) : R2 := if x ∈ gammaR h R then x else refl x

open Classical in
/-- Eq. (2.3), p. 5: the operator `P`,
`Pφ = φ + (K_k φ - i η S_k φ) + (K_k^{re} φ - i η S_k^{re} φ)` on `Γ_R` and
`Pφ = φ/2 + (K_k φ - i η S_k φ) + (K_k^{re} φ - i η S_k^{re} φ)` on `∂B_R^- ∪ {x_A, x_B}`. -/
def opP (k eta : ℝ) (h : ℝ → ℝ) (R : ℝ) (phi : R2 → ℂ) (x : R2) : ℂ :=
  (if x ∈ gammaR h R then phi x else phi x / 2) + combinedPot k eta h R phi x +
    combinedPot k eta h R phi (psiRe h R x)

open Classical in
/-- Eq. (2.4), p. 5: `g = -2(u^i + u^r)` on `Γ_R` and `g = 0` on `∂B_R^- ∪ {x_A, x_B}`. -/
def gData (k : ℝ) (d : R2) (h : ℝ → ℝ) (R : ℝ) (x : R2) : ℂ :=
  if x ∈ gammaR h R then -2 * (uInc k d x + uRefl k d x) else 0

/-- Section 2, p. 5: a solution `u^s` of (DP), defined on `\overline{D_+}`, extended into
`ℝ²_- \ \overline{B_R}` by `u^s(x) = -u^s(x^{re})`. -/
def reflExt (h : ℝ → ℝ) (u : R2 → ℂ) (x : R2) : ℂ := if h (x 0) ≤ x 1 then u x else -u (refl x)

/-- Remark 2.6, eq. (2.8), p. 9: the far field pattern of the combined layer potential,
`u^∞(x̂) = e^{-iπ/4}/√(8πk) ∫_{∂D_R^-} [k ν(y) · x̂ + η] e^{-ik x̂ · y} φ(y) ds(y)`. -/
def farFieldFormula (k eta : ℝ) (h : ℝ → ℝ) (R : ℝ) (phi : R2 → ℂ) (xhat : R2) : ℂ :=
  Complex.exp (-(Complex.I * (Real.pi : ℂ) / 4)) / (Real.sqrt (8 * Real.pi * k) : ℂ) *
    bdryInt h R (fun y nu =>
      ((k * dot nu xhat + eta : ℝ) : ℂ) * Complex.exp (-(Complex.I * (k : ℂ) * (dot xhat y : ℂ))) *
        phi y)

/-! ### The graded-mesh parameterisation (Section 3, p. 9) -/

/-- Section 3, p. 9: Kress's function
`v(s) = (1/p - 1/2)((π - 2s)/π)³ + (1/p)(2s - π)/π + 1/2`. -/
def kressV (p : ℕ) (s : ℝ) : ℝ :=
  (1 / (p : ℝ) - 1 / 2) * ((Real.pi - 2 * s) / Real.pi) ^ 3 +
    1 / (p : ℝ) * ((2 * s - Real.pi) / Real.pi) + 1 / 2

/-- Section 3, p. 9: `ω(s) = π v(s)^p / (v(s)^p + v(π - s)^p)` for `0 ≤ s ≤ π`. -/
def kressOmega0 (p : ℕ) (s : ℝ) : ℝ :=
  Real.pi * kressV p s ^ p / (kressV p s ^ p + kressV p (Real.pi - s) ^ p)

/-- Section 3, p. 9: the grading function `ω : [0, 2π] → [0, 2π]`, given by `kressOmega0` on
`[0, π]` and by `ω(s) = ω(s - π) + π` for `π < s ≤ 2π`. -/
def kressOmega (p : ℕ) (s : ℝ) : ℝ :=
  if s ≤ Real.pi then kressOmega0 p s else kressOmega0 p (s - Real.pi) + Real.pi

/-- Section 3, p. 9: the parameterisation `x(s)` of `∂D_R^-`, `0 ≤ s ≤ 2π`, with `p = 4`:
`x(s) = (-2Rω(s)/π + R, h_Γ(-2Rω(s)/π + R))` for `0 ≤ s ≤ π` and
`x(s) = (R cos ω(s), R sin ω(s))` for `π < s ≤ 2π`. -/
def gradedPt (R : ℝ) (h : ℝ → ℝ) (s : ℝ) : R2 :=
  if s ≤ Real.pi then
    pt (-2 * R * kressOmega 4 s / Real.pi + R) (h (-2 * R * kressOmega 4 s / Real.pi + R))
  else pt (R * Real.cos (kressOmega 4 s)) (R * Real.sin (kressOmega 4 s))

/-- Section 3, p. 9: the unit normal `ν(x(s))` of `∂D_R^-` pointing out of `D_R^-`. -/
def gradedNormal (R : ℝ) (h : ℝ → ℝ) (s : ℝ) : R2 :=
  if s ≤ Real.pi then gNormal h (-2 * R * kressOmega 4 s / Real.pi + R)
  else pt (Real.cos (kressOmega 4 s)) (Real.sin (kressOmega 4 s))

/-- Section 3, p. 9: the speed `|x'(s)|` of the parameterisation. -/
def gradedSpeed (R : ℝ) (h : ℝ → ℝ) (s : ℝ) : ℝ := ‖deriv (gradedPt R h) s‖

/-- Section 3, p. 9: the parameterised integral
`∫_0^{2π} [∂Φ_k(z, x(s))/∂ν(x(s)) - i η Φ_k(z, x(s))] φ(x(s)) |x'(s)| ds`. -/
def paramInt (k eta R : ℝ) (h : ℝ → ℝ) (phi : R2 → ℂ) (z : R2) : ℂ :=
  ∫ s in (0 : ℝ)..(2 * Real.pi),
    (dPhi k z (gradedPt R h s) (gradedNormal R h s) -
        Complex.I * (eta : ℂ) * Phi k z (gradedPt R h s)) *
      phi (gradedPt R h s) * (gradedSpeed R h s : ℂ)

/-! ### The inverse problem (Section 4, pp. 10-11) -/

/-- Section 4, p. 11: `C²_{0,R}(ℝ) = {h ∈ C²(ℝ) : supp(h) ⊂ (-R, R)}`. -/
def C20R (R : ℝ) : Set (ℝ → ℝ) := {g | ContDiff ℝ 2 g ∧ tsupport g ⊆ Set.Ioo (-R) R}

/-- Section 4, p. 11: the norm `‖g‖_{C²(ℝ)} = sup |g| + sup |g'| + sup |g''|`, used for `g ∈ C²_{0,R}`. -/
def c2Norm (g : ℝ → ℝ) : ℝ :=
  (⨆ t, |g t|) + (⨆ t, |deriv g t|) + ⨆ t, |iteratedDeriv 2 g t|

/-- Section 4, p. 11: the norm in `L²(S_+)`,
`‖F‖_{L²(S_+)} = (∫_0^π |F(cos θ, sin θ)|² dθ)^{1/2}`. -/
def l2NormUpper (F : R2 → ℂ) : ℝ :=
  Real.sqrt (∫ θ in (0 : ℝ)..Real.pi, ‖F (pt (Real.cos θ) (Real.sin θ))‖ ^ 2)

/-- Theorem 4.2, p. 11: the normal derivative `∂u/∂ν` at the point `(t, h_Γ(t))` of `Γ`, `ν`
the unit normal directed into `D_+`, as the one-sided derivative from `D_+`. -/
def normalDerivGam (h : ℝ → ℝ) (u : R2 → ℂ) (t : ℝ) : ℂ :=
  derivWithin (fun s : ℝ => u (pt t (h t) + s • gNormal h t)) (Set.Ici 0) 0

/-- Theorem 4.2, p. 11: the boundary data `f = -(ν₂ Δh) ∂u/∂ν` on `Γ` of the derivative `u'`,
where `u = u^i + u^r + u^s` is the total field and `ν₂` the second component of `ν`. -/
def domainDerivData (k : ℝ) (d : R2) (h : ℝ → ℝ) (us : R2 → ℂ) (dh : ℝ → ℝ) (x : R2) : ℂ :=
  -(((gNormal h (x 0)) 1 * dh (x 0) : ℝ) : ℂ) *
    normalDerivGam h (fun y => uInc k d y + uRefl k d y + us y) (x 0)

/-! ### The spline basis (Remark 5.1, p. 12) -/

/-- Remark 5.1, p. 12: the truncated power `z_+^m = z^m` for `z ≥ 0` and `0` for `z < 0`. -/
def truncPow (m : ℕ) (z : ℝ) : ℝ := if 0 ≤ z then z ^ m else 0

/-- Remark 5.1, p. 12: `φ(t) = ∑_{j=0}^{m+1} (-1)^j/m! · C(m+1, j) · (t + (m+1)/2 - j)_+^m`
(the paper writes `k` for the degree `m` and chooses `k = 4`). -/
def splinePhi (m : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 2), (-1 : ℝ) ^ j / (m.factorial : ℝ) * ((m + 1).choose j : ℝ) *
    truncPow m (t + ((m : ℝ) + 1) / 2 - j)

/-- Remark 5.1, p. 12: the mesh width `h = 2R/(M + 5)`. -/
def splineStep (R : ℝ) (M : ℕ) : ℝ := 2 * R / ((M : ℝ) + 5)

/-- Remark 5.1, p. 12: the knots `t_i = (i + 2)h - R`. -/
def splineKnot (R : ℝ) (M i : ℕ) : ℝ := ((i : ℝ) + 2) * splineStep R M - R

/-- Remark 5.1, p. 12: the basis function `φ_i(t) = φ((t - t_i)/h)` of `R_M`, with `k = 4`. -/
def splineBasis (R : ℝ) (M i : ℕ) (t : ℝ) : ℝ :=
  splinePhi 4 ((t - splineKnot R M i) / splineStep R M)

end Arxiv1302_0161


