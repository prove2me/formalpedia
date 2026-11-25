-- Prove2me | Definitions.Def_Arxiv2108_02600_Basic
-- name    : Arxiv2108_02600_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T09:37:14.806418+00:00
-- url     : https://prove2.me/theorems/cd87b229-b416-5a4b-801e-18320adea21c
-- title:
--   Elastic Green's tensors, the Dirichlet rough-surface problem, kernel splittings and the Nyström scheme
-- statement:
--   Objects of Sections 2–4 of Li, Liu, Zhang and Zhang (2021), *The Nyström method for elastic wave scattering by unbounded rough surfaces*.
--
--   1. **Parameters.** Lamé constants $\lambda,\mu$ with $\mu>0$, $\lambda+2\mu>0$, frequency $\omega>0$; $c_s=\mu^{-1/2}$, $c_p=(\lambda+2\mu)^{-1/2}$, $\kappa_s=c_s\omega$, $\kappa_p=c_p\omega$; and, as fixed throughout the paper by (2.10), $\tilde\mu=\frac{\mu(\lambda+\mu)}{\lambda+3\mu}$, $\tilde\lambda=\frac{(\lambda+\mu)(\lambda+2\mu)}{\lambda+3\mu}$.
--   2. **Bessel and Hankel functions** of integer order $n$ at $z>0$, by their ascending series [CK19, (3.97)–(3.98)]:
--   $$J_n(z)=\sum_{p\ge0}\frac{(-1)^p}{p!(n+p)!}\Big(\frac z2\Big)^{n+2p},$$
--   $$Y_n(z)=\frac2\pi\Big(\ln\frac z2+C_E\Big)J_n(z)-\frac1\pi\sum_{p=0}^{n-1}\frac{(n-1-p)!}{p!}\Big(\frac2z\Big)^{n-2p}-\frac1\pi\sum_{p\ge0}\frac{(-1)^p}{p!(n+p)!}\Big(\frac z2\Big)^{n+2p}\big(\phi(p)+\phi(n+p)\big),$$
--   with $\phi(0)=0$, $\phi(p)=\sum_{m=1}^p\frac1m$, $C_E$ Euler's constant, and $H^{(1)}_n=J_n+iY_n$.
--   3. **Green's tensors.** $\Phi(x,y,\kappa)=\frac i4H_0^{(1)}(\kappa|x-y|)$; the free-space tensor (2.7) $G(x,y)=\frac1\mu\Phi(x,y,\kappa_s)I+\omega^{-2}\nabla_x\nabla_x^\top(\Phi(x,y,\kappa_s)-\Phi(x,y,\kappa_p))$; for a level $a$, $y'=(y_1,2a-y_2)$ and
--   $$U(x,y)=-\frac{i}{2\pi\omega^2}\int_{\mathbb R}\big[M_p+M_s\big](\tau)\,e^{-i(x_1-y_1)\tau}\,d\tau,$$
--   with $\gamma_{p,s}=\sqrt{\kappa_{p,s}^2-\tau^2}$ (imaginary part $\ge0$), $M_p=\frac{e^{i\gamma_p(x_2+y_2-2a)}-e^{i(\gamma_p(x_2-a)+\gamma_s(y_2-a))}}{\gamma_p\gamma_s+\tau^2}\begin{pmatrix}-\tau^2\gamma_s&\tau^3\\\tau\gamma_p\gamma_s&-\tau^2\gamma_p\end{pmatrix}$, $M_s=\frac{e^{i\gamma_s(x_2+y_2-2a)}-e^{i(\gamma_s(x_2-a)+\gamma_p(y_2-a))}}{\gamma_p\gamma_s+\tau^2}\begin{pmatrix}-\tau^2\gamma_s&-\tau\gamma_p\gamma_s\\-\tau^3&-\tau^2\gamma_p\end{pmatrix}$; and the half-plane Dirichlet tensor (2.6) $G_{D,a}(x,y)=G(x,y)-G(x,y')+U(x,y)$.
--   4. **Stress operator (2.5)** with normal $\nu$: $P\varphi=(\mu+\tilde\mu)\partial_\nu\varphi+\tilde\lambda\,\nu\,\mathrm{div}\,\varphi-\tilde\mu\,\nu^\perp\mathrm{div}^\perp\varphi$, $\nu^\perp=(\nu_2,-\nu_1)$, $\mathrm{div}^\perp\varphi=\partial_2\varphi_1-\partial_1\varphi_2$; the double-layer kernel of a tensor $G$ is $\Pi_{jk}(x,y)=(P^{(y)}G_{j\cdot}(x,y)^\top)_k$.
--   5. **Surface and spaces.** $f\in B^{(n)}_{c,M}$ means $f\in BC^{n+2}(\mathbb R)$, $\max_{l\le n+2}\sup|f^{(l)}|\le M$, $\inf f\ge c$. On $\Gamma=\{x_2=f(x_1)\}$: $x(s)=(s,f(s))$, $r=|x(s)-y(t)|$, $\nu(t)=(-f'(t),1)/\sqrt{1+f'(t)^2}$, $l(t)=(-f'(t),1)$, $l^\perp(t)=(1,f'(t))$. $BC^n$ (bounded derivatives of order $\le n$), $C^n_{0,\pi}(\mathbb R^2)$ (in $BC^n$, vanishing for $|s-t|\ge\pi$), $BC^n_p(\mathbb R^2)$ (derivatives of order $\le n$ bounded by a multiple of $(1+|s-t|)^{-p}$).
--   6. **Problem (DP).** $\Omega=\{x_2>f(x_1)\}$. $u\in[C^2(\Omega)\cap C(\overline\Omega)\cap H^1_{\rm loc}(\Omega)]^2$ solves $\mu\Delta u+(\lambda+\mu)\nabla\nabla\cdot u+\omega^2u=0$ in $\Omega$, $u=g$ on $\Gamma$, the UPRC (2.3) (for some $H>\sup f$ and $\phi\in[L^\infty(\Gamma_H)]^2$, $u(x)=\int_{\Gamma_H}\Pi^{(2)}_{D,H}(x,y)\phi(y)\,ds(y)$ for $x_2>H$, built from $G_{D,H}$ with $\nu=(0,1)$), and $\sup_{x\in\Omega}|x_2|^\beta|u(x)|<\infty$ for some $\beta$. Data: $g\in[BC(\Gamma)\cap H^{1/2}_{\rm loc}(\Gamma)]^2$.
--   7. **Integral equation (2.15).** $(D\psi)(s)=2\int\Pi^{(2)}_{D,h}(x(s),y(t))\psi(t)\sqrt{1+f'(t)^2}\,dt$, $(S\psi)(s)=2\int G_{D,h}(x(s),y(t))\psi(t)\sqrt{1+f'(t)^2}\,dt$, and $(I+D-i\eta S)\psi=2g$.
--   8. **Kernels of Section 3.** $A^{(1)}=2G\sqrt{1+f'^2}$ (kernel of $S_1$), $B^{(1)}$ from (3.8), $C^{(1)}=A^{(1)}-B^{(1)}\ln|s-t|$; $A^{(2)}=2[P^{(y)}G_{j\cdot}]_k\sqrt{1+f'^2}$ (kernel of $D_1$), $B^{(2)}$ from (3.16), $C^{(2)}=A^{(2)}-B^{(2)}\ln|s-t|$; $A^{(3)}$ the kernel of $D_2-i\eta S_2$ built from $G(x,y')-U(x,y)$; $A$ the kernel of $D-i\eta S$; $B^*=-i\eta B^{(1)}+B^{(2)}$, $C^*=-i\eta C^{(1)}+C^{(2)}-A^{(3)}$; the cut-off $\chi$; $B=\pi B^*\chi(s-t)$ and $C=B^*[(1-\chi)\ln|s-t|-\chi\ln\frac{\sin((s-t)/2)}{(s-t)/2}]+C^*$, both extended to $s=t$ by their limits.
--   9. **Notation of the proof of Theorem 4.1.** $\rho_n(\kappa,s,t)=H^{(1)}_n(\kappa r)-\frac{2i}\pi J_n(\kappa r)\ln|s-t|$, $\gamma_1=(\kappa_s\rho_1(\kappa_s)-\kappa_p\rho_1(\kappa_p))/r$, $\gamma_2=\kappa_s^2\rho_2(\kappa_s)-\kappa_p^2\rho_2(\kappa_p)$, $\gamma_3=r[\kappa_s^3\rho_3(\kappa_s)-\kappa_p^3\rho_3(\kappa_p)]$, $\xi=((s-t)f'(t)+f(t)-f(s))/r^2$, $\zeta_{jk}=(x_j-y_j)(x_k-y_k)/r^2$, and $\sigma_{jk}$ as defined there.
--   10. **Nyström scheme (4.2).** Knots $t_j=-\mathrm{cut}+j\pi/N$, $j\in\mathbb Z$; weights $R^{(N)}_j(s)=-\frac1N[\sum_{m=1}^{N-1}\frac1m\cos m(s-t_j)+\frac1{2N}\cos N(s-t_j)]$; the equation $\psi_N(s)+\sum_{j\in\mathbb Z}[R^{(N)}_j(s)B(s,t_j)+\frac\pi NC(s,t_j)]\psi_N(t_j)=2g(s)$ for all $s$.
--
--   **Formalization Note** Points are `Fin 2 → ℝ`, and the paper's indices $1,2$ are Lean's $0,1$. $J_n$ and $Y_n$ are defined by the series that the paper cites. The branch of $\gamma_{p,s}$ is not stated in the paper; the one with nonnegative imaginary part is used, because it makes the integrand of $U$ decay. In the printed $M_p$ and $M_s$, a misplaced brace puts the second exponential inside the exponent of the first; it is read as a difference of two exponentials. With these two readings, a numerical check gives $G_{D,a}=0$ on $x_2=a$. The paper defines the diagonal values $B(s,s)$ and $C(s,s)$ through (3.14), (3.15), (3.18) and (3.19). Here they are the limits as $t\to s$, because (3.15) and (3.19) are not those limits (see the report). $H^{1/2}_{\rm loc}(\Gamma)$ is expressed in the parameter $s$ through the Gagliardo seminorm on bounded intervals. $H^1_{\rm loc}(\Omega)$ follows the paper's definition: $H^1$ on open sets whose closures are compact subsets of $\Omega$. Integrals and series in (2.13)–(2.15), (2.3) and (4.2) are required to converge absolutely.
-- source:
--   J. Li, X. Liu, B. Zhang and H. Zhang, The Nyström method for elastic wave scattering by unbounded rough surfaces, arXiv:2108.02600v1 (2021), Section 2 (eqs. (2.1)-(2.15), (DP)), Section 3 (eqs. (3.1)-(3.25)), Section 4 (proof of Theorem 4.1, eq. (4.2)), Section 5 (plane waves before (5.3))

import Mathlib

/-!
J. Li, X. Liu, B. Zhang and H. Zhang, *The Nyström method for elastic wave scattering by
unbounded rough surfaces*, arXiv:2108.02600v1 (2021): Bessel and Hankel functions, the free-space
and half-plane Dirichlet Green's tensors, the generalized stress operator, the Dirichlet problem
(DP) and the boundary integral equation (2.15) of Section 2, the kernel splittings of Section 3,
the notation of the proof of Theorem 4.1 and the Nyström scheme (4.2) of Section 4.

Points of `ℝ²` are `Fin 2 → ℝ`; the paper's indices `1, 2` are Lean's `0, 1`.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace Arxiv2108_02600

/-- Section 2: points `x = (x₁, x₂)` of `ℝ²`, written `x 0`, `x 1`. -/
abbrev Pt := Fin 2 → ℝ

/-- Section 2, after (2.1): Lamé constants `λ, μ` with `μ > 0`, `λ + 2μ > 0`, and angular
frequency `ω > 0`. -/
structure Lame where
  /-- `λ` -/
  lam : ℝ
  /-- `μ` -/
  mu : ℝ
  /-- `ω` -/
  omega : ℝ
  mu_pos : 0 < mu
  lam_two_mu_pos : 0 < lam + 2 * mu
  omega_pos : 0 < omega

namespace Lame

variable (P : Lame)

/-- Section 2, after (2.7): `c_s = μ^{-1/2}`. -/
def cs : ℝ := 1 / Real.sqrt P.mu

/-- Section 2, after (2.7): `c_p = (λ + 2μ)^{-1/2}`. -/
def cp : ℝ := 1 / Real.sqrt (P.lam + 2 * P.mu)

/-- Section 2, after (2.7): shear wavenumber `κ_s = c_s ω`. -/
def ks : ℝ := P.cs * P.omega

/-- Section 2, after (2.7): compressional wavenumber `κ_p = c_p ω`. -/
def kp : ℝ := P.cp * P.omega

/-- Eq. (2.10): `μ̃ = μ(λ+μ)/(λ+3μ)`, fixed throughout the paper. -/
def muT : ℝ := P.mu * (P.lam + P.mu) / (P.lam + 3 * P.mu)

/-- Eq. (2.10): `λ̃ = (λ+μ)(λ+2μ)/(λ+3μ)`, fixed throughout the paper. -/
def lamT : ℝ := (P.lam + P.mu) * (P.lam + 2 * P.mu) / (P.lam + 3 * P.mu)

end Lame

/-! ### Bessel and Hankel functions (Section 2, with [CK19, (3.97)–(3.98)] cited in Section 3) -/

/-- Section 2: the Bessel function `J_n` of integer order `n`, by its ascending series
[CK19, (3.97)]: `J_n(z) = ∑_{p≥0} (-1)^p / (p!(n+p)!) (z/2)^{n+2p}`. -/
def besselJ (n : ℕ) (z : ℝ) : ℝ :=
  ∑' p : ℕ, (-1 : ℝ) ^ p / ((p.factorial : ℝ) * ((n + p).factorial : ℝ)) * (z / 2) ^ (n + 2 * p)

/-- Proof of Theorem 4.1 (after (4.9)): `φ(0) = 0`, `φ(p) = ∑_{m=1}^p 1/m`. -/
def phiH (p : ℕ) : ℝ := (harmonic p : ℝ)

/-- Section 2: the Neumann function `Y_n` of integer order `n` at `z > 0`, by its ascending series
[CK19, (3.98)]: `Y_n(z) = (2/π)(ln(z/2) + C_E) J_n(z) - (1/π) ∑_{p=0}^{n-1} (n-1-p)!/p! (2/z)^{n-2p}
- (1/π) ∑_{p≥0} (-1)^p/(p!(n+p)!) (z/2)^{n+2p} (φ(p) + φ(n+p))`. -/
def besselY (n : ℕ) (z : ℝ) : ℝ :=
  2 / Real.pi * (Real.log (z / 2) + Real.eulerMascheroniConstant) * besselJ n z
  - 1 / Real.pi * ∑ p ∈ Finset.range n,
      ((n - 1 - p).factorial : ℝ) / (p.factorial : ℝ) * (2 / z) ^ ((n : ℤ) - 2 * (p : ℤ))
  - 1 / Real.pi * ∑' p : ℕ, (-1 : ℝ) ^ p / ((p.factorial : ℝ) * ((n + p).factorial : ℝ)) *
      (z / 2) ^ (n + 2 * p) * (phiH p + phiH (n + p))

/-- Section 2: the Hankel function of the first kind `H_n^{(1)} = J_n + i Y_n`. -/
def hankel1 (n : ℕ) (z : ℝ) : ℂ := (besselJ n z : ℂ) + Complex.I * (besselY n z : ℂ)

/-! ### Green's tensors and the stress operator (Section 2) -/

/-- Section 2: the Euclidean distance `|x - y|` in `ℝ²`. -/
def dist2 (x y : Pt) : ℝ := Real.sqrt ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2)

/-- Section 2, after (2.7): the fundamental solution of the Helmholtz equation,
`Φ(x, y, κ) = (i/4) H_0^{(1)}(κ|x - y|)`. -/
def helmholtzFS (k : ℝ) (x y : Pt) : ℂ := Complex.I / 4 * hankel1 0 (k * dist2 x y)

/-- The partial derivative `∂F/∂x_j` of `F : ℝ² → ℂ` at `x`. -/
def pd (j : Fin 2) (F : Pt → ℂ) (x : Pt) : ℂ := fderiv ℝ F x (Pi.single j 1)

/-- Eq. (2.7): the free-space Green's tensor of the Navier equation,
`G(x,y) = (1/μ) Φ(x,y,κ_s) I + ω^{-2} ∇_x ∇_xᵀ (Φ(x,y,κ_s) - Φ(x,y,κ_p))`, `x ≠ y`. -/
def greenFree (P : Lame) (x y : Pt) : Matrix (Fin 2) (Fin 2) ℂ := fun j k =>
  (if j = k then helmholtzFS P.ks x y / (P.mu : ℂ) else 0) +
    1 / (P.omega : ℂ) ^ 2 * pd j (pd k (fun z => helmholtzFS P.ks z y - helmholtzFS P.kp z y)) x

/-- Section 2: the reflection `y' = (y₁, 2a - y₂)` in the line `x₂ = a`. -/
def reflect (a : ℝ) (y : Pt) : Pt := ![y 0, 2 * a - y 1]

/-- The square root `√u` of a real number taken with nonnegative imaginary part
(`i√(-u)` for `u < 0`), the branch for `γ_p, γ_s` in the definition of `U` (Section 2). -/
def sqrtBranch (u : ℝ) : ℂ :=
  if 0 ≤ u then (Real.sqrt u : ℂ) else Complex.I * (Real.sqrt (-u) : ℂ)

/-- Section 2, after (2.7): the matrix function
`U(x,y) = -(i/(2πω²)) ∫_ℝ [M_p + M_s](τ, γ_p, γ_s; x₂, y₂) e^{-i(x₁-y₁)τ} dτ` for the line
`x₂ = a`, with `γ_p = √(κ_p² - τ²)`, `γ_s = √(κ_s² - τ²)`,
`M_p = (e^{iγ_p(x₂+y₂-2a)} - e^{i(γ_p(x₂-a)+γ_s(y₂-a))}) / (γ_pγ_s + τ²) [[-τ²γ_s, τ³], [τγ_pγ_s, -τ²γ_p]]`,
`M_s = (e^{iγ_s(x₂+y₂-2a)} - e^{i(γ_s(x₂-a)+γ_p(y₂-a))}) / (γ_pγ_s + τ²) [[-τ²γ_s, -τγ_pγ_s], [-τ³, -τ²γ_p]]`. -/
def greenU (P : Lame) (a : ℝ) (x y : Pt) : Matrix (Fin 2) (Fin 2) ℂ := fun j k =>
  -(Complex.I / (2 * (Real.pi : ℂ) * (P.omega : ℂ) ^ 2)) * ∫ τ : ℝ,
    (let gp := sqrtBranch (P.kp ^ 2 - τ ^ 2)
     let gs := sqrtBranch (P.ks ^ 2 - τ ^ 2)
     let tc : ℂ := (τ : ℂ)
     let den := gp * gs + tc ^ 2
     let ep := Complex.exp (Complex.I * gp * ((x 1 + y 1 - 2 * a : ℝ) : ℂ)) -
       Complex.exp (Complex.I * (gp * ((x 1 - a : ℝ) : ℂ) + gs * ((y 1 - a : ℝ) : ℂ)))
     let es := Complex.exp (Complex.I * gs * ((x 1 + y 1 - 2 * a : ℝ) : ℂ)) -
       Complex.exp (Complex.I * (gs * ((x 1 - a : ℝ) : ℂ) + gp * ((y 1 - a : ℝ) : ℂ)))
     (ep / den * (!![-tc ^ 2 * gs, tc ^ 3; tc * gp * gs, -tc ^ 2 * gp] : Matrix (Fin 2) (Fin 2) ℂ) j k +
      es / den * (!![-tc ^ 2 * gs, -tc * gp * gs; -tc ^ 3, -tc ^ 2 * gp] : Matrix (Fin 2) (Fin 2) ℂ) j k) *
       Complex.exp (-Complex.I * ((x 0 - y 0 : ℝ) : ℂ) * tc))

/-- Eq. (2.6): the Green's tensor of the Navier equation in the half-plane `{x₂ > a}` with
Dirichlet condition on `{x₂ = a}`: `G_{D,a}(x,y) = G(x,y) - G(x,y') + U(x,y)`. -/
def greenDH (P : Lame) (a : ℝ) (x y : Pt) : Matrix (Fin 2) (Fin 2) ℂ :=
  greenFree P x y - greenFree P x (reflect a y) + greenU P a x y

/-- Eq. (2.5): the generalized stress vector `Pφ = (μ+μ̃) ∂φ/∂ν + λ̃ ν div φ - μ̃ ν^⊥ div^⊥ φ`
of a vector field `φ` at `y`, with normal `ν`, `ν^⊥ = (ν₂, -ν₁)`, `div^⊥ φ = ∂₂φ₁ - ∂₁φ₂`, and
`μ̃, λ̃` from (2.10). -/
def stressOp (P : Lame) (nu : Fin 2 → ℝ) (phi : Pt → Fin 2 → ℂ) (y : Pt) : Fin 2 → ℂ := fun m =>
  ((P.mu + P.muT : ℝ) : ℂ) * ∑ q : Fin 2, pd q (fun z => phi z m) y * (nu q : ℂ)
    + (P.lamT : ℂ) * (nu m : ℂ) * (pd 0 (fun z => phi z 0) y + pd 1 (fun z => phi z 1) y)
    - (P.muT : ℂ) * ((![nu 1, -nu 0] : Fin 2 → ℝ) m : ℂ) *
      (pd 1 (fun z => phi z 0) y - pd 0 (fun z => phi z 1) y)

/-- Eqs. (2.4), (3.4): the double-layer kernel `Π_{jk}(x,y) = (P^{(y)} (G_{j·}(x,y))ᵀ)_k`
of a Green's tensor `G`, the stress operator acting in `y` with normal `ν`. -/
def piKernel (P : Lame) (G : Pt → Pt → Matrix (Fin 2) (Fin 2) ℂ) (nu : Fin 2 → ℝ) (x y : Pt) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun j k => stressOp P nu (fun z m => G x z j m) y k

/-! ### The rough surface and function spaces (Section 2) -/

/-- Section 2: `BC^n(ℝ^m)`-type class: `u` is `C^n` and its derivatives of order `≤ n` are
bounded. -/
def IsBCn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (n : ℕ) (u : E → F) : Prop :=
  ContDiff ℝ n u ∧ ∀ m ≤ n, ∃ K : ℝ, ∀ x, ‖iteratedFDeriv ℝ m u x‖ ≤ K

/-- Section 2: `BC(ℝ)`: bounded continuous functions. -/
def IsBC {F : Type*} [NormedAddCommGroup F] (u : ℝ → F) : Prop :=
  Continuous u ∧ ∃ K : ℝ, ∀ x, ‖u x‖ ≤ K

/-- Section 2: the norm of `BC^n(ℝ)`, the largest sup-norm of a derivative of order `≤ n`. -/
def bcnNorm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ) (u : ℝ → F) : ℝ :=
  sSup {a : ℝ | ∃ m ≤ n, ∃ x : ℝ, a = ‖iteratedFDeriv ℝ m u x‖}

/-- Section 2: `C^n_{0,π}(ℝ²) = {a ∈ BC^n(ℝ²) : a(s,t) = 0 for |s - t| ≥ π}`. -/
def IsC0pi (n : ℕ) (a : ℝ × ℝ → ℂ) : Prop :=
  IsBCn n a ∧ ∀ s t : ℝ, Real.pi ≤ |s - t| → a (s, t) = 0

/-- Section 2: `BC^n_p(ℝ²)`: `a ∈ BC^n(ℝ²)` whose derivatives of order `≤ n` are bounded by a
multiple of `(1 + |s - t|)^{-p}`. -/
def IsBCnp (n : ℕ) (p : ℝ) (a : ℝ × ℝ → ℂ) : Prop :=
  IsBCn n a ∧ ∃ K : ℝ, ∀ m ≤ n, ∀ x : ℝ × ℝ, (1 + |x.1 - x.2|) ^ p * ‖iteratedFDeriv ℝ m a x‖ ≤ K

/-- Section 2: `f ∈ B^{(n)}_{c,M}`: `f ∈ BC^{n+2}(ℝ)` with `‖f‖_{BC^{n+2}} ≤ M` and
`inf f ≥ c`. -/
def InB (n : ℕ) (c M : ℝ) (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ (n + 2 : ℕ) f ∧ (∀ l ≤ n + 2, ∀ x, |iteratedDeriv l f x| ≤ M) ∧ ∀ x, c ≤ f x

/-- Section 2: the point `x(s) = (s, f(s))` of the surface `Γ = {x₂ = f(x₁)}`. -/
def surfPt (f : ℝ → ℝ) (s : ℝ) : Pt := ![s, f s]

/-- Section 2: the arclength factor `√(1 + f'(t)²)`. -/
def jac (f : ℝ → ℝ) (t : ℝ) : ℝ := Real.sqrt (1 + deriv f t ^ 2)

/-- Section 3.1: the upward unit normal `ν(t) = (-f'(t), 1)/√(1 + f'(t)²)` at `y(t)`. -/
def normal (f : ℝ → ℝ) (t : ℝ) : Fin 2 → ℝ := ![-deriv f t / jac f t, 1 / jac f t]

/-- Section 3.1: `l(t) = √(1 + f'(t)²) ν(t) = (-f'(t), 1)`. -/
def lvec (f : ℝ → ℝ) (t : ℝ) : Fin 2 → ℝ := ![-deriv f t, 1]

/-- Section 3.1: `l^⊥(t) = √(1 + f'(t)²) ν^⊥(t) = (1, f'(t))`. -/
def lperp (f : ℝ → ℝ) (t : ℝ) : Fin 2 → ℝ := ![1, deriv f t]

/-- Section 3.1: `r(s,t) = |x(s) - y(t)| = √((s-t)² + (f(s)-f(t))²)`. -/
def rdist (f : ℝ → ℝ) (s t : ℝ) : ℝ := dist2 (surfPt f s) (surfPt f t)

/-- Section 3.1: the components `x_j(s) - y_j(t)` of `x(s) - y(t)`. -/
def dvec (f : ℝ → ℝ) (s t : ℝ) (j : Fin 2) : ℝ := surfPt f s j - surfPt f t j

/-! ### The Dirichlet problem (DP) (Section 2) -/

/-- Section 2: the domain `Ω = {x : x₂ > f(x₁)}` above the surface. -/
def domainAbove (f : ℝ → ℝ) : Set Pt := {x | f (x 0) < x 1}

/-- Eq. (2.1): the Navier operator `μΔu + (λ+μ)∇∇·u + ω²u`. -/
def navierOp (P : Lame) (u : Pt → Fin 2 → ℂ) (x : Pt) : Fin 2 → ℂ := fun m =>
  (P.mu : ℂ) * (pd 0 (pd 0 (fun z => u z m)) x + pd 1 (pd 1 (fun z => u z m)) x)
    + ((P.lam + P.mu : ℝ) : ℂ) * pd m (fun z => pd 0 (fun w => u w 0) z + pd 1 (fun w => u w 1) z) x
    + (P.omega : ℂ) ^ 2 * u x m

/-- Section 2: `u ∈ H¹(V)`: `u ∈ L²(V)` with weak first derivatives in `L²(V)`. -/
def IsH1On (V : Set Pt) (u : Pt → ℂ) : Prop :=
  MemLp u 2 (volume.restrict V) ∧ ∃ v : Fin 2 → Pt → ℂ, (∀ i, MemLp (v i) 2 (volume.restrict V)) ∧
    ∀ φ : Pt → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ V → ∀ i : Fin 2,
      ∫ x in V, u x * (fderiv ℝ φ x (Pi.single i 1) : ℂ) = -∫ x in V, v i x * (φ x : ℂ)

/-- Section 2: `u ∈ H¹_loc(Ω)`: `u ∈ H¹(V)` for every open `V` whose closure is a compact subset
of `Ω`. -/
def IsH1Loc (Ω : Set Pt) (u : Pt → ℂ) : Prop :=
  ∀ V : Set Pt, IsOpen V → IsCompact (closure V) → closure V ⊆ Ω → IsH1On V u

/-- Section 2: `H^{1/2}_loc(Γ)` in the parameter `s` of `x(s) = (s, f(s))`: on every bounded
interval `[a,b]`, `u ∈ L²` and the Gagliardo seminorm `∫∫ |u(s)-u(t)|²/|s-t|² ds dt` is finite. -/
def IsHalfLoc (u : ℝ → ℂ) : Prop :=
  ∀ a b : ℝ, AEStronglyMeasurable u (volume.restrict (Set.Icc a b)) ∧
    (∫⁻ s in Set.Icc a b, ‖u s‖ₑ ^ 2) < ⊤ ∧
    (∫⁻ p in Set.Icc a b ×ˢ Set.Icc a b, ‖u p.1 - u p.2‖ₑ ^ 2 / ‖p.1 - p.2‖ₑ ^ 2) < ⊤

/-- Section 2, (DP): the boundary data `g ∈ [BC(Γ) ∩ H^{1/2}_loc(Γ)]²`. -/
def IsDPData (f : ℝ → ℝ) (g : Pt → Fin 2 → ℂ) : Prop :=
  ContinuousOn g {x | x 1 = f (x 0)} ∧ (∃ K : ℝ, ∀ s, ‖g (surfPt f s)‖ ≤ K) ∧
    ∀ m : Fin 2, IsHalfLoc (fun s => g (surfPt f s) m)

/-- Eqs. (2.3)–(2.4): the upward propagating radiation condition: for some `H > sup f` and some
`φ ∈ [L^∞(Γ_H)]²`, `u(x) = ∫_{Γ_H} Π^{(2)}_{D,H}(x,y) φ(y) ds(y)` for `x₂ > H`, where `Π^{(2)}_{D,H}`
is built from `G_{D,H}` with the normal `ν = (0,1)` of `Γ_H` pointing into `U_H`. -/
def SatisfiesUPRC (P : Lame) (f : ℝ → ℝ) (u : Pt → Fin 2 → ℂ) : Prop :=
  ∃ H : ℝ, BddAbove (Set.range f) ∧ sSup (Set.range f) < H ∧
    ∃ φ : ℝ → Fin 2 → ℂ, MemLp φ ⊤ volume ∧ ∀ x : Pt, H < x 1 → ∀ j : Fin 2,
      Integrable (fun y1 : ℝ => ∑ k, piKernel P (greenDH P H) ![0, 1] x ![y1, H] j k * φ y1 k) ∧
      u x j = ∫ y1 : ℝ, ∑ k, piKernel P (greenDH P H) ![0, 1] x ![y1, H] j k * φ y1 k

/-- Eq. (2.8): the vertical growth rate condition `sup_{x ∈ Ω} |x₂|^β |u(x)| < ∞` for some
`β ∈ ℝ` (supremum in `[0, ∞]`). -/
def SatisfiesGrowth (f : ℝ → ℝ) (u : Pt → Fin 2 → ℂ) : Prop :=
  ∃ β : ℝ, (⨆ x ∈ domainAbove f, ENNReal.ofReal |x 1| ^ β * ‖u x‖ₑ) < ⊤

/-- Section 2, (DP): `u ∈ [C²(Ω) ∩ C(Ω̄) ∩ H¹_loc(Ω)]²` solves the Navier equation (2.1) in `Ω`,
equals `g` on `Γ`, and satisfies the UPRC (2.3) and the growth condition (2.8). -/
def IsDPSolution (P : Lame) (f : ℝ → ℝ) (g u : Pt → Fin 2 → ℂ) : Prop :=
  ContDiffOn ℝ 2 u (domainAbove f) ∧ ContinuousOn u (closure (domainAbove f)) ∧
    (∀ m : Fin 2, IsH1Loc (domainAbove f) (fun x => u x m)) ∧
    (∀ x ∈ domainAbove f, navierOp P u x = 0) ∧
    (∀ s : ℝ, u (surfPt f s) = g (surfPt f s)) ∧ SatisfiesUPRC P f u ∧ SatisfiesGrowth f u

/-- Section 5, eq. (5.2): the compressional plane wave `u_p^{inc}(x;θ) = θ e^{iκ_p x·θ}`. -/
def planeWaveP (P : Lame) (θ : Fin 2 → ℝ) (x : Pt) : Fin 2 → ℂ := fun m =>
  (θ m : ℂ) * Complex.exp (Complex.I * (P.kp : ℂ) * ((x 0 * θ 0 + x 1 * θ 1 : ℝ) : ℂ))

/-- Section 5, eq. (5.2): the shear plane wave `u_s^{inc}(x;θ) = θ^⊥ e^{iκ_s x·θ}`,
`θ^⊥ = (θ₂, -θ₁)`. -/
def planeWaveS (P : Lame) (θ : Fin 2 → ℝ) (x : Pt) : Fin 2 → ℂ := fun m =>
  ((![θ 1, -θ 0] : Fin 2 → ℝ) m : ℂ) *
    Complex.exp (Complex.I * (P.ks : ℂ) * ((x 0 * θ 0 + x 1 * θ 1 : ℝ) : ℂ))

/-! ### The boundary integral equation (Section 2) -/

/-- Eq. (2.13): `(Dψ)(s) = 2 ∫ Π^{(2)}_{D,h}(x(s), y(t)) ψ(t) √(1 + f'(t)²) dt`. -/
def opD (P : Lame) (h : ℝ) (f : ℝ → ℝ) (psi : ℝ → Fin 2 → ℂ) (s : ℝ) : Fin 2 → ℂ := fun j =>
  2 * ∫ t : ℝ, (∑ k, piKernel P (greenDH P h) (normal f t) (surfPt f s) (surfPt f t) j k * psi t k) *
    (jac f t : ℂ)

/-- Eq. (2.14): `(Sψ)(s) = 2 ∫ G_{D,h}(x(s), y(t)) ψ(t) √(1 + f'(t)²) dt`. -/
def opS (P : Lame) (h : ℝ) (f : ℝ → ℝ) (psi : ℝ → Fin 2 → ℂ) (s : ℝ) : Fin 2 → ℂ := fun j =>
  2 * ∫ t : ℝ, (∑ k, greenDH P h (surfPt f s) (surfPt f t) j k * psi t k) * (jac f t : ℂ)

/-- Eq. (2.15): `ψ` solves `(I + D - iηS) ψ = 2g`, the integrals in (2.13)–(2.14) being absolutely
convergent. -/
def SolvesBIE (P : Lame) (η : ℂ) (h : ℝ) (f : ℝ → ℝ) (g psi : ℝ → Fin 2 → ℂ) : Prop :=
  ∀ s : ℝ, (∀ j : Fin 2,
      Integrable (fun t => (∑ k, piKernel P (greenDH P h) (normal f t) (surfPt f s) (surfPt f t) j k *
        psi t k) * (jac f t : ℂ)) ∧
      Integrable (fun t => (∑ k, greenDH P h (surfPt f s) (surfPt f t) j k * psi t k) * (jac f t : ℂ))) ∧
    psi s + opD P h f psi s - (Complex.I * η) • opS P h f psi s = (2 : ℂ) • g s

/-! ### Kernels of Section 3 -/

/-- Section 3.1: the kernel of `S₁`, `A^{(1)}_{jk}(s,t) = 2 G_{jk}(x(s), y(t)) √(1 + f'(t)²)`. -/
def kerA1 (P : Lame) (f : ℝ → ℝ) (s t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := fun j k =>
  2 * greenFree P (surfPt f s) (surfPt f t) j k * (jac f t : ℂ)

/-- Eq. (3.8): `B^{(1)}_{jk} = (1/π){[-(1/μ)J₀(κ_s r) + ω^{-2}(κ_s J₁(κ_s r) - κ_p J₁(κ_p r))/r] δ_{jk}
- ω^{-2} (κ_s² J₂(κ_s r) - κ_p² J₂(κ_p r))/r² (x_j - y_j)(x_k - y_k)} √(1 + f'(t)²)`. -/
def kerB1 (P : Lame) (f : ℝ → ℝ) (s t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := fun j k =>
  let r := rdist f s t
  (((1 / Real.pi) * ((if j = k then
      -(1 / P.mu) * besselJ 0 (P.ks * r) +
        1 / P.omega ^ 2 * (P.ks * besselJ 1 (P.ks * r) - P.kp * besselJ 1 (P.kp * r)) / r
      else 0) -
    1 / P.omega ^ 2 * (P.ks ^ 2 * besselJ 2 (P.ks * r) - P.kp ^ 2 * besselJ 2 (P.kp * r)) / r ^ 2 *
      (dvec f s t j * dvec f s t k)) * jac f t : ℝ) : ℂ)

/-- Eq. (3.9): `C^{(1)} = A^{(1)} - B^{(1)} ln|s - t|`. -/
def kerC1 (P : Lame) (f : ℝ → ℝ) (s t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := fun j k =>
  kerA1 P f s t j k - kerB1 P f s t j k * (Real.log |s - t| : ℂ)

/-- Section 3.2: the kernel of `D₁`, `A^{(2)}_{jk}(s,t) = 2 [P^{(y)} (G_{j·}(x,y))ᵀ]_k √(1 + f'(t)²)`
at `x = x(s)`, `y = y(t)`, with the normal `ν(t)`. -/
def kerA2 (P : Lame) (f : ℝ → ℝ) (s t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := fun j k =>
  2 * piKernel P (greenFree P) (normal f t) (surfPt f s) (surfPt f t) j k * (jac f t : ℂ)

/-- Eq. (3.16): the coefficient `B^{(2)}` of `ln|s - t|` in `A^{(2)}`. -/
def kerB2 (P : Lame) (f : ℝ → ℝ) (s t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := fun j k =>
  let r := rdist f s t
  let j1 := P.ks * besselJ 1 (P.ks * r) / r
  let j2 := P.ks ^ 2 * besselJ 2 (P.ks * r) - P.kp ^ 2 * besselJ 2 (P.kp * r)
  let j3 := P.ks ^ 3 * besselJ 3 (P.ks * r) - P.kp ^ 3 * besselJ 3 (P.kp * r)
  let xn := (s - t) * deriv f t + f t - f s
  let d := dvec f s t
  ((((P.mu + P.muT) * (((if j = k then 1 else 0) * (1 / (Real.pi * P.mu) * j1 -
        1 / (Real.pi * P.omega ^ 2) * j2 / r ^ 2)) +
      1 / (Real.pi * P.omega ^ 2) * j3 / r ^ 3 * (d j * d k)) * xn)
    + (P.mu + P.muT) * (1 / (Real.pi * P.omega ^ 2)) * j2 / r ^ 2 * (d j * lvec f t k + d k * lvec f t j)
    + P.lamT * (-(1 / (Real.pi * P.mu)) * j1 + 4 / (Real.pi * P.omega ^ 2) * j2 / r ^ 2 -
        1 / (Real.pi * P.omega ^ 2) * j3 / r) * (d j * lvec f t k)
    + P.muT * (1 / (Real.pi * P.mu)) * j1 *
        ((f s - f t) * (if j = 0 then 1 else 0) - (s - t) * (if j = 1 then 1 else 0)) * lperp f t k
    : ℝ) : ℂ)

/-- Eq. (3.17): `C^{(2)} = A^{(2)} - B^{(2)} ln|s - t|`. -/
def kerC2 (P : Lame) (f : ℝ → ℝ) (s t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := fun j k =>
  kerA2 P f s t j k - kerB2 P f s t j k * (Real.log |s - t| : ℂ)

/-- Eqs. (3.5)–(3.6): the tensor `G(x, y') - U(x, y)` entering `D₂` and `S₂` (level `a`). -/
def greenRefl (P : Lame) (a : ℝ) (x y : Pt) : Matrix (Fin 2) (Fin 2) ℂ :=
  greenFree P x (reflect a y) - greenU P a x y

/-- Section 3.3: the kernel `A^{(3)}` of `D₂ - iηS₂` (eqs. (3.3), (3.5), (3.6)):
`2 {[P^{(y)} (G_{j·}(x,y') - U_{j·}(x,y))ᵀ]_k - iη (G_{jk}(x,y') - U_{jk}(x,y))} √(1 + f'(t)²)`. -/
def kerA3 (P : Lame) (η : ℂ) (h : ℝ) (f : ℝ → ℝ) (s t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := fun j k =>
  2 * (piKernel P (greenRefl P h) (normal f t) (surfPt f s) (surfPt f t) j k -
    Complex.I * η * greenRefl P h (surfPt f s) (surfPt f t) j k) * (jac f t : ℂ)

/-- Eqs. (2.13)–(2.14), (3.21): the kernel `A(s,t)` of `D - iηS`,
`2 [Π^{(2)}_{D,h}(x(s),y(t)) - iη G_{D,h}(x(s),y(t))] √(1 + f'(t)²)`. -/
def kerA (P : Lame) (η : ℂ) (h : ℝ) (f : ℝ → ℝ) (s t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := fun j k =>
  2 * (piKernel P (greenDH P h) (normal f t) (surfPt f s) (surfPt f t) j k -
    Complex.I * η * greenDH P h (surfPt f s) (surfPt f t) j k) * (jac f t : ℂ)

/-- Eq. (3.22): `B^* = -iη B^{(1)} + B^{(2)}`. -/
def kerBstar (P : Lame) (η : ℂ) (f : ℝ → ℝ) (s t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (-(Complex.I * η)) • kerB1 P f s t + kerB2 P f s t

/-- Eq. (3.23): `C^* = -iη C^{(1)} + C^{(2)} - A^{(3)}`. -/
def kerCstar (P : Lame) (η : ℂ) (h : ℝ) (f : ℝ → ℝ) (s t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (-(Complex.I * η)) • kerC1 P f s t + kerC2 P f s t - kerA3 P η h f s t

/-- Section 3, after (3.25): the cut-off `χ(s) = 1` for `|s| ≤ 1`,
`χ(s) = [1 + exp(1/(π - |s|) + 1/(1 - |s|))]^{-1}` for `1 < |s| < π`, `χ(s) = 0` for `|s| ≥ π`. -/
def cutoff (s : ℝ) : ℝ :=
  if |s| ≤ 1 then 1
  else if |s| < Real.pi then (1 + Real.exp (1 / (Real.pi - |s|) + 1 / (1 - |s|)))⁻¹
  else 0

/-- The value at `(s,t)` of a kernel defined off the diagonal, extended to `t = s` by its limit
as `t → s` (the diagonal values of Section 3 are these limits). -/
def diagLim (F : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ) (s t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  if t = s then limUnder (𝓝[≠] s) (F s) else F s t

/-- Eq. (3.24): `B(s,t) = π B^*(s,t) χ(s - t)`, extended to `s = t` by continuity
(the diagonal value of Section 3, end). -/
def kerB (P : Lame) (η : ℂ) (f : ℝ → ℝ) : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ :=
  diagLim (fun s t => ((Real.pi * cutoff (s - t) : ℝ) : ℂ) • kerBstar P η f s t)

/-- Eq. (3.25): `C(s,t) = B^*(s,t)[(1 - χ(s-t)) ln|s-t| - χ(s-t) ln(sin((s-t)/2)/((s-t)/2))]
+ C^*(s,t)`, extended to `s = t` by continuity (the diagonal value of Section 3, end). -/
def kerC (P : Lame) (η : ℂ) (h : ℝ) (f : ℝ → ℝ) : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ :=
  diagLim (fun s t =>
    (((1 - cutoff (s - t)) * Real.log |s - t| -
        cutoff (s - t) * Real.log (Real.sin ((s - t) / 2) / ((s - t) / 2)) : ℝ) : ℂ) •
      kerBstar P η f s t + kerCstar P η h f s t)

/-! ### Notation of the proof of Theorem 4.1 (Section 4, p. 15) -/

/-- Proof of Theorem 4.1: `ρ_n(κ,s,t) = H_n^{(1)}(κr) - (2i/π) J_n(κr) ln|s - t|`. -/
def rhoN (f : ℝ → ℝ) (n : ℕ) (k s t : ℝ) : ℂ :=
  hankel1 n (k * rdist f s t) -
    2 * Complex.I / (Real.pi : ℂ) * (besselJ n (k * rdist f s t) : ℂ) * (Real.log |s - t| : ℂ)

/-- Proof of Theorem 4.1: `γ₁ = (κ_s ρ₁(κ_s) - κ_p ρ₁(κ_p))/r`. -/
def gam1 (P : Lame) (f : ℝ → ℝ) (s t : ℝ) : ℂ :=
  ((P.ks : ℂ) * rhoN f 1 P.ks s t - (P.kp : ℂ) * rhoN f 1 P.kp s t) / (rdist f s t : ℂ)

/-- Proof of Theorem 4.1: `γ₂ = κ_s² ρ₂(κ_s) - κ_p² ρ₂(κ_p)`. -/
def gam2 (P : Lame) (f : ℝ → ℝ) (s t : ℝ) : ℂ :=
  (P.ks : ℂ) ^ 2 * rhoN f 2 P.ks s t - (P.kp : ℂ) ^ 2 * rhoN f 2 P.kp s t

/-- Proof of Theorem 4.1: `γ₃ = r [κ_s³ ρ₃(κ_s) - κ_p³ ρ₃(κ_p)]`. -/
def gam3 (P : Lame) (f : ℝ → ℝ) (s t : ℝ) : ℂ :=
  (rdist f s t : ℂ) * ((P.ks : ℂ) ^ 3 * rhoN f 3 P.ks s t - (P.kp : ℂ) ^ 3 * rhoN f 3 P.kp s t)

/-- Proof of Theorem 4.1: `ξ(s,t) = ((s - t) f'(t) + f(t) - f(s)) / r²`. -/
def xiF (f : ℝ → ℝ) (s t : ℝ) : ℝ := ((s - t) * deriv f t + f t - f s) / rdist f s t ^ 2

/-- Proof of Theorem 4.1: `ζ_{jk}(s,t) = (x_j(s) - y_j(t))(x_k(s) - y_k(t)) / r²`. -/
def zetaF (f : ℝ → ℝ) (s t : ℝ) (j k : Fin 2) : ℝ := dvec f s t j * dvec f s t k / rdist f s t ^ 2

/-- Proof of Theorem 4.1: `σ_{jk} = -(μ+μ̃)(i/(2ω²)) (γ₂/r²) [(x_j-y_j) l_k + (x_k-y_k) l_j]
+ λ̃ [(i/(2μ)) (κ_s/r) ρ₁(κ_s) - (2i/ω²) γ₂/r² + (i/(2ω²)) γ₃/r²] (x_j-y_j) l_k
- μ̃ (i/(2μ)) (κ_s/r) ρ₁(κ_s) [(f(s)-f(t)) δ_{j1} - (s-t) δ_{j2}] l^⊥_k`. -/
def sigmaF (P : Lame) (f : ℝ → ℝ) (s t : ℝ) (j k : Fin 2) : ℂ :=
  let r : ℂ := (rdist f s t : ℂ)
  let d := dvec f s t
  let I := Complex.I
  ((P.mu + P.muT : ℝ) : ℂ) * (-I) / (2 * (P.omega : ℂ) ^ 2) * gam2 P f s t / r ^ 2 *
      ((d j * lvec f t k + d k * lvec f t j : ℝ) : ℂ)
    + (P.lamT : ℂ) * (I / (2 * (P.mu : ℂ)) * (P.ks : ℂ) / r * rhoN f 1 P.ks s t -
        2 * I / (P.omega : ℂ) ^ 2 * gam2 P f s t / r ^ 2 +
        I / (2 * (P.omega : ℂ) ^ 2) * gam3 P f s t / r ^ 2) * ((d j * lvec f t k : ℝ) : ℂ)
    - (P.muT : ℂ) * I / (2 * (P.mu : ℂ)) * (P.ks : ℂ) / r * rhoN f 1 P.ks s t *
        (((f s - f t) * (if j = 0 then 1 else 0) - (s - t) * (if j = 1 then 1 else 0)) *
          lperp f t k : ℝ)

/-! ### The Nyström scheme (Section 4) -/

/-- Section 4: the knots `t_j = -cut + jπ/N`, `j ∈ ℤ`. -/
def knot (cut : ℝ) (N : ℕ) (j : ℤ) : ℝ := -cut + j * Real.pi / N

/-- Section 4: the quadrature weights
`R_j^{(N)}(s) = -(1/N)[∑_{m=1}^{N-1} (1/m) cos m(s - t_j) + (1/(2N)) cos N(s - t_j)]`. -/
def quadR (cut : ℝ) (N : ℕ) (j : ℤ) (s : ℝ) : ℝ :=
  -(1 / (N : ℝ)) * (∑ m ∈ Finset.Ico 1 N, 1 / (m : ℝ) * Real.cos (m * (s - knot cut N j)) +
    1 / (2 * (N : ℝ)) * Real.cos (N * (s - knot cut N j)))

/-- Eq. (4.2): the `j`-th term `α_j^{(N)}(s) ψ(t_j)` with
`α_j^{(N)}(s) = R_j^{(N)}(s) B(s,t_j) + (π/N) C(s,t_j)`. -/
def nystromTerm (P : Lame) (η : ℂ) (h : ℝ) (f : ℝ → ℝ) (cut : ℝ) (N : ℕ)
    (psi : ℝ → Fin 2 → ℂ) (s : ℝ) (j : ℤ) : Fin 2 → ℂ :=
  ((quadR cut N j s : ℂ) • kerB P η f s (knot cut N j) +
      ((Real.pi / N : ℝ) : ℂ) • kerC P η h f s (knot cut N j)).mulVec (psi (knot cut N j))

/-- Eq. (4.2): `ψ_N(s) + ∑_{j ∈ ℤ} α_j^{(N)}(s) ψ_N(t_j) = 2 g(s)` for all `s ∈ ℝ`, the series
being convergent. -/
def SolvesNystrom (P : Lame) (η : ℂ) (h : ℝ) (f : ℝ → ℝ) (cut : ℝ) (N : ℕ)
    (g psiN : ℝ → Fin 2 → ℂ) : Prop :=
  ∀ s : ℝ, Summable (nystromTerm P η h f cut N psiN s) ∧
    psiN s + ∑' j : ℤ, nystromTerm P η h f cut N psiN s j = (2 : ℂ) • g s

end Arxiv2108_02600


