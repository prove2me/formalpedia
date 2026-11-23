-- Prove2me | Definitions.Def_RoughSurfaceScattering_Basic
-- name    : RoughSurfaceScattering_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-23T20:54:37.259804+00:00
-- url     : https://prove2.me/theorems/93e2bc3e-e7dd-40a7-b8b5-27322fbca3a0
-- title:
--   Rough-surface transmission scattering: fundamental solutions, radiation conditions, the TSP and its integral operator
-- statement:
--   Objects of Sections 2, 4, 5 and 6 of Wu and Yang, *Direct and inverse acoustic scattering by global rough surfaces* (arXiv:2406.06129v2).
--
--   1. **Fundamental solutions.** $\Phi_k(x,y)=\frac i4H_0^{(1)}(k|x-y|)$ for $k>0$ and $\Phi_0(x,y)=\frac1{2\pi}\ln\frac1{|x-y|}$, where $H_0^{(1)}=J_0+iY_0$ with $J_0(x)=\sum_{m\ge0}\frac{(-1)^m(x/2)^{2m}}{(m!)^2}$ and $Y_0(x)=\frac2\pi\big(\ln\frac x2+\gamma\big)J_0(x)+\frac2\pi\sum_{m\ge1}\frac{(-1)^{m+1}H_m(x/2)^{2m}}{(m!)^2}$ ($H_m$ the harmonic numbers, $\gamma$ Euler's constant).
--   2. **Interface.** For $f:\mathbb R\to\mathbb R$, $D^\pm=\{x_2\gtrless f(x_1)\}$, $\Gamma=\{(s,f(s))\}$, $f^-=\inf f$, $f^+=\sup f$, $U_h^\pm=\{x_2\gtrless h\}$. The unit normal $n=(f',-1)/\sqrt{1+f'^2}$ points out of $D^+$ (into $D^-$), and $n'=-n$ points into $D^+$; arc length is $ds=\sqrt{1+f'(s)^2}\,ds_1$. $f\in BC^{1,\alpha}(\mathbb R)$ means $f,f'$ bounded and continuous and $f'$ uniformly $\alpha$-Hölder; $f\in C^{2,\lambda}(\mathbb R)$ means $f\in C^2$ with $f''$ uniformly $\lambda$-Hölder.
--   3. **Spaces on $\Gamma$.** Functions on $\Gamma$ are written as functions of $s$. $BC(\Gamma)$: bounded continuous; $BC^{0,\alpha}(\Gamma)$: in addition uniformly $\alpha$-Hölder in the Euclidean distance of points of $\Gamma$, with norm $\|\varphi\|_{0,\alpha,\Gamma}=\|\varphi\|_{\infty,\Gamma}+\sup_{x\ne y}|\varphi(x)-\varphi(y)|/|x-y|^\alpha$; $BC^{1,\alpha}(\Gamma)$: $\varphi\in BC(\Gamma)$ with surface gradient $\operatorname{Grad}\varphi\in BC^{0,\alpha}(\Gamma)$, norm $\|\varphi\|_{\infty,\Gamma}+\|\operatorname{Grad}\varphi\|_{0,\alpha,\Gamma}$.
--   4. **Regularity on closed sets.** $u\in C^1(S)$ means $u$ and a gradient field $Du$ are continuous on $S$ and $Du$ is the derivative of $u$ at interior points; $BC^1(S)$ adds boundedness of $u$ and $Du$ on $S$.
--   5. **Radiation conditions (Definition 2.2).** $v\in\mathrm{UPRC}(G,k)$ if $\Delta v+k^2v=0$ in $G$ and, for some $h$ and $\varphi\in L^\infty(\Gamma_h)$, $U_h^+\subseteq G$ and $v(x)=2\int_{\Gamma_h}\partial_{y_2}\Phi_k(x,y)\varphi(y)\,ds(y)$ on $U_h^+$; $\mathrm{DPRC}$ uses $U_h^-$ and the factor $-2$.
--   6. **Transmission Scattering Problem (Section 2).** $(u_+,u_-)$ solves the TSP for $(\Gamma,k_-,k_+,\mu)$ with data $(g_1,g_2)$ if, for some $h_+>f^+$ and $h_-<f^-$: $u_\pm\in C^2(D^\pm)$, $u_+\in BC^1(\overline{D^+}\setminus U_{h_+}^+)$, $u_-\in BC^1(\overline{D^-}\setminus U_{h_-}^-)$; $\Delta u_\pm+k_\pm^2u_\pm=0$ in $D^\pm$; $u_+-u_-=g_1$ and $\partial_nu_+-\mu\partial_nu_-=g_2$ on $\Gamma$; $\sup_{D^\pm}|x_2|^\beta|u_\pm(x)|<\infty$ for some $\beta\in\mathbb R$; $u_+\in\mathrm{UPRC}(D^+,k_+)$, $u_-\in\mathrm{DPRC}(D^-,k_-)$. An incident field $u^i$ produces the data $g_1=-u^i|_\Gamma$, $g_2=-\partial_nu^i|_\Gamma$ (problem (2.1)); the point source is $\Phi_k(\cdot,z)$ and the hypersingular source is $\nabla_x\Phi_k(\cdot,z)\cdot\nu$. The scatterer conditions are $k_\pm,\mu>0$, $(\mu-1)(k_+^2-k_-^2\mu)\ge0$, $k_+^2\ne k_-^2\mu$.
--   7. **Impedance Green's function (2.8).** $G_k^{\pm(\mathcal I)}(x,y;a)=\Phi_k(x,y)+\Phi_k(x,y_a')+P_k^\pm(x-y_a')$, $y_a'=(y_1,2a-y_2)$, with $P_k^\pm(z)=\frac{|z|e^{ik|z|}}\pi\int_0^\infty\frac{t^{-1/2}e^{-k|z|t}[|z|\pm z_2(1+it)]}{\sqrt{t-2i}\,[|z|t-i(|z|\pm z_2)]^2}dt$ (principal square root).
--   8. **Layer potentials and $\mathcal M$ (Section 4).** $\mathcal S^\pm_{k,a}\psi(x)=\int_\Gamma G^{\pm(\mathcal I)}_k(x,y;a)\psi(y)ds(y)$, $\mathcal D^\pm_{k,a}\varphi(x)=\int_\Gamma\partial_{n'(y)}G^{\pm(\mathcal I)}_k(x,y;a)\varphi(y)ds(y)$, with the upward normal $n'=-n$. On $\Gamma$, $S,K,K'$ have kernels $G$, $\partial_{n'(y)}G$, $\partial_{n'(x)}G$, and
--   $$\mathcal M=\begin{pmatrix}K^+_{k_+,h_-}-\mu^{-1}K^-_{k_-,h_+}+\frac{1+\mu}{2\mu}I & S^+_{k_+,h_-}-\mu^{-1}S^-_{k_-,h_+}\\ T^-_{k_-,h_+}-T^+_{k_+,h_-} & K'^-_{k_-,h_+}-K'^+_{k_+,h_-}+I\end{pmatrix},$$
--   where $T^--T^+$ is the integral operator with kernel $\partial_{n'(x)}\partial_{n'(y)}\big(G^{-(\mathcal I)}_{k_-}(x,y;h_+)-G^{+(\mathcal I)}_{k_+}(x,y;h_-)\big)$. $L^p(\Gamma)$ is taken with respect to arc length.
--   9. **Sobolev quantities and domains.** $W^{2,p}(U)$: $u$ and its weak derivatives of order $1$ and $2$ (tested against $C_c^\infty(U)$) lie in $L^p(U)$. $\|w\|_{H^1(D)}=\big(\int_D|w|^2+|\partial_1w|^2+|\partial_2w|^2\big)^{1/2}$ (possibly $\infty$). A bounded $C^{2,\lambda}$ domain is a bounded connected open set which, near each boundary point and in rotated or reflected coordinates, lies below the graph of a $C^{2,\lambda}$ function. $n(y)$ on $\partial D_0$ is the outward unit normal and $ds$ the arc length ($1$-dimensional Hausdorff measure). $v_j$ is the correction term of Theorem 5.3, and $\Gamma_{c,d}=\{(x_1,c):|x_1|\le d\}$.
--
--   **Formalization Note** Points of $\mathbb R^2$ are elements of `EuclideanSpace ℝ (Fin 2)`. Functions on $\Gamma$ are functions of the parameter $s=x_1$, but Hölder quotients use the Euclidean distance of the points $(s,f(s))$ and $L^p(\Gamma)$ uses arc length. The boundary values and normal derivatives of $u_\pm$ on $\Gamma$ are the continuous extensions supplied by the $BC^1$ condition. The weak-derivative tests use real-valued test functions, which is equivalent to complex-valued ones by linearity. The paper states that $n$ points out of $D^+$ but its jump relations (4.19)–(4.20) and its matrix $\mathcal M$ are correct only if the layer potentials and $K,K',T$ use the normal $n'=-n$ pointing into $D^+$; with $n$ in the potentials the ansatz leads to a different matrix. The formalization therefore uses $n'$ in the potentials and in $\mathcal M$, and $n$ in the TSP condition and the incident data, which is the only reading under which the printed $\mathcal M$ is the reduction of the TSP.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Section 2 (fundamental solutions, Definition 2.2, TSP, eq. (2.8)), Section 4 (layer potentials, operator M, eq. (4.3)/(4.14)), Sections 5-6 (Sobolev norms, C^{2,lambda} domains, v_j, Gamma_{c,d})

import Mathlib

/-!
C. Wu and J. Yang, *Direct and inverse acoustic scattering by global rough surfaces*,
arXiv:2406.06129v2: the fundamental solutions, the rough interface, the upward/downward
propagating radiation conditions and the Transmission Scattering Problem (TSP) of Section 2,
the impedance half-plane Green's functions (2.8), the layer potentials and the boundary integral
operator `M` of Section 4, and the Sobolev quantities and domains used in Sections 5 and 6.

Points of `ℝ²` are elements of `EuclideanSpace ℝ (Fin 2)`; the paper's `x = (x₁, x₂)` is
`x 0 = x₁`, `x 1 = x₂`. A function on the interface `Γ = {(s, f s)}` is written as a function of
the parameter `s = x₁`.
-/

open MeasureTheory

noncomputable section

namespace RoughSurfaceScattering

/-- The plane `ℝ²` with its Euclidean norm. -/
abbrev R2 := EuclideanSpace ℝ (Fin 2)

/-- The point `(a, b) ∈ ℝ²`. -/
def pt (a b : ℝ) : R2 := !₂[a, b]

/-! ### Fundamental solutions (Section 2, p. 4) -/

/-- The Bessel function `J₀(x) = ∑_{m ≥ 0} (-1)^m (x/2)^{2m} / (m!)²` (used in `H₀^{(1)}`,
Section 2, p. 4). -/
def besselJ0 (x : ℝ) : ℝ :=
  ∑' m : ℕ, (-1 : ℝ) ^ m * (x / 2) ^ (2 * m) / ((m.factorial : ℝ) ^ 2)

/-- The Bessel function of the second kind, for `x > 0`:
`Y₀(x) = (2/π)(log(x/2) + γ) J₀(x) + (2/π) ∑_{m ≥ 1} (-1)^{m+1} H_m (x/2)^{2m} / (m!)²`,
with `H_m` the harmonic numbers and `γ` the Euler–Mascheroni constant (used in `H₀^{(1)}`,
Section 2, p. 4). -/
def besselY0 (x : ℝ) : ℝ :=
  2 / Real.pi * (Real.log (x / 2) + Real.eulerMascheroniConstant) * besselJ0 x +
    2 / Real.pi * ∑' m : ℕ, (-1 : ℝ) ^ m * (harmonic (m + 1) : ℝ) * (x / 2) ^ (2 * (m + 1)) /
      (((m + 1).factorial : ℝ) ^ 2)

/-- The Hankel function of the first kind of order zero, `H₀^{(1)} = J₀ + i Y₀`, for `x > 0`
(Section 2, p. 4). -/
def hankel01 (x : ℝ) : ℂ := (besselJ0 x : ℂ) + Complex.I * (besselY0 x : ℂ)

/-- Section 2, p. 4: the fundamental solution `Φ_k(x,y) = (i/4) H₀^{(1)}(k|x-y|)` of the
Helmholtz equation for `k > 0`, and `Φ₀(x,y) = (1/2π) ln(1/|x-y|)` for the Laplacian (`k = 0`).
Only `x ≠ y` and `k ≥ 0` are used. -/
def Phi (k : ℝ) (x y : R2) : ℂ :=
  if k = 0 then ((1 / (2 * Real.pi) * Real.log (1 / ‖x - y‖) : ℝ) : ℂ)
  else Complex.I / 4 * hankel01 (k * ‖x - y‖)

/-- `∂Φ_k(x,y)/∂y₂`, the kernel of the radiation conditions (2.3), Definition 2.2, p. 5. -/
def dPhi_dy2 (k : ℝ) (x y : R2) : ℂ :=
  deriv (fun t : ℝ => Phi k x (pt (y 0) t)) (y 1)

/-! ### Half planes and the rough interface (Section 2, pp. 4-5) -/

/-- `U_h^+ = {x : x₂ > h}` (Section 2, p. 4). -/
def Uplus (h : ℝ) : Set R2 := {x | h < x 1}

/-- `U_h^- = {x : x₂ < h}` (Section 2, p. 4). -/
def Uminus (h : ℝ) : Set R2 := {x | x 1 < h}

/-- `D^+ = {x : x₂ > f(x₁)}`, the region above the interface (Section 2, p. 4). -/
def Dplus (f : ℝ → ℝ) : Set R2 := {x | f (x 0) < x 1}

/-- `D^- = {x : x₂ < f(x₁)}`, the region below the interface (Section 2, p. 4). -/
def Dminus (f : ℝ → ℝ) : Set R2 := {x | x 1 < f (x 0)}

/-- `f^- = inf f` (Section 2, p. 4). -/
def finf (f : ℝ → ℝ) : ℝ := ⨅ t, f t

/-- `f^+ = sup f` (Section 2, p. 4). -/
def fsup (f : ℝ → ℝ) : ℝ := ⨆ t, f t

/-- The point `(s, f(s))` of the interface `Γ` (Section 2, p. 4). -/
def gpt (f : ℝ → ℝ) (s : ℝ) : R2 := pt s (f s)

/-- The arc-length density `ds = √(1 + f'(s)²) ds₁` on `Γ`. -/
def arcDen (f : ℝ → ℝ) (s : ℝ) : ℝ := Real.sqrt (1 + deriv f s ^ 2)

/-- The arc-length measure on `Γ`, written in the parameter `s = x₁`. -/
def arcMeasure (f : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun s => ENNReal.ofReal (arcDen f s))

/-- Section 2, p. 4: the unit normal `n` to `Γ` at `(s, f(s))` pointing out of `D^+`,
`n = (f'(s), -1) / √(1 + f'(s)²)`. -/
def normal (f : ℝ → ℝ) (s : ℝ) : R2 := (arcDen f s)⁻¹ • pt (deriv f s) (-1)

/-- The unit normal to `Γ` pointing into `D^+`, `-n`. The layer potentials and the kernels of
`K, K', T` in Section 4 use this orientation: it is the one for which the jump relations
(4.19)–(4.20) and the printed operator `M` are consistent with the TSP conditions, which keep `n`. -/
def normalUp (f : ℝ → ℝ) (s : ℝ) : R2 := -normal f s

/-- Section 2, p. 3: `f ∈ BC^{1,α}(ℝ)`: `f` and `f'` are bounded and continuous and `f'` is
uniformly Hölder continuous with exponent `α`. With `α = 1` this is `Γ ∈ BC^{1,1}` (Section 4). -/
def IsBC1Alpha (α : ℝ) (f : ℝ → ℝ) : Prop :=
  Differentiable ℝ f ∧ Continuous (deriv f) ∧ (∃ C, ∀ t, |f t| ≤ C) ∧
    (∃ C, ∀ t, |deriv f t| ≤ C) ∧ ∃ C, ∀ s t, |deriv f s - deriv f t| ≤ C * |s - t| ^ α

/-- Theorem 5.2 (p. 17): `f ∈ C^{2,λ}(ℝ)`: `f` is twice continuously differentiable and `f''`
is uniformly Hölder continuous with exponent `λ`. -/
def IsC2Lambda (lam : ℝ) (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧
    ∃ C, ∀ s t, |iteratedDeriv 2 f s - iteratedDeriv 2 f t| ≤ C * |s - t| ^ lam

/-! ### Function spaces on `Γ` (Section 2, p. 3) -/

/-- `φ ∈ BC(Γ)`: bounded and continuous on `Γ` (Section 2, p. 3). -/
def IsBCGam (φ : ℝ → ℂ) : Prop := Continuous φ ∧ ∃ C, ∀ s, ‖φ s‖ ≤ C

/-- `φ ∈ BC^{0,α}(Γ)`: bounded, continuous and uniformly Hölder continuous with exponent `α`
in the Euclidean distance of points of `Γ` (Section 2, p. 3). -/
def IsBC0AlphaGam {E : Type*} [NormedAddCommGroup E] (f : ℝ → ℝ) (α : ℝ) (φ : ℝ → E) : Prop :=
  Continuous φ ∧ (∃ C, ∀ s, ‖φ s‖ ≤ C) ∧
    ∃ C, ∀ s t, ‖φ s - φ t‖ ≤ C * ‖gpt f s - gpt f t‖ ^ α

/-- The surface gradient `Grad φ` on `Γ`: the arc-length derivative of `φ` times the unit
tangent `(1, f'(s))/√(1+f'(s)²)` (Section 2, p. 3). -/
def surfGrad (f : ℝ → ℝ) (φ : ℝ → ℂ) (s : ℝ) : EuclideanSpace ℂ (Fin 2) :=
  !₂[deriv φ s / ((1 + deriv f s ^ 2 : ℝ) : ℂ),
     deriv φ s * ((deriv f s : ℝ) : ℂ) / ((1 + deriv f s ^ 2 : ℝ) : ℂ)]

/-- `φ ∈ BC^{1,α}(Γ) = {φ ∈ BC(Γ) : Grad φ ∈ BC^{0,α}(Γ)}` (Section 2, p. 3). -/
def IsBC1AlphaGam (f : ℝ → ℝ) (α : ℝ) (φ : ℝ → ℂ) : Prop :=
  IsBCGam φ ∧ Differentiable ℝ φ ∧ IsBC0AlphaGam f α (surfGrad f φ)

/-- `‖φ‖_{∞,Γ} = sup_Γ |φ|` (Section 2, p. 3); used only for bounded `φ`. -/
def supNormGam {E : Type*} [NormedAddCommGroup E] (φ : ℝ → E) : ℝ := ⨆ s, ‖φ s‖

/-- `‖φ‖_{0,α,Γ} = ‖φ‖_{∞,Γ} + sup_{x ≠ y} |φ(x) - φ(y)| / |x - y|^α` (Section 2, p. 3); used
only for `φ ∈ BC^{0,α}(Γ)`. -/
def holderNorm0 {E : Type*} [NormedAddCommGroup E] (f : ℝ → ℝ) (α : ℝ) (φ : ℝ → E) : ℝ :=
  supNormGam φ + ⨆ p : {p : ℝ × ℝ // p.1 ≠ p.2},
    ‖φ p.1.1 - φ p.1.2‖ / ‖gpt f p.1.1 - gpt f p.1.2‖ ^ α

/-- `‖φ‖_{1,α,Γ} = ‖φ‖_{∞,Γ} + ‖Grad φ‖_{0,α,Γ}` (Section 2, p. 3). -/
def holderNorm1 (f : ℝ → ℝ) (α : ℝ) (φ : ℝ → ℂ) : ℝ :=
  supNormGam φ + holderNorm0 f α (surfGrad f φ)

/-! ### Regularity classes on subsets of `ℝ²` (Section 2, p. 3) -/

/-- `u ∈ C¹(S)` on a closed set `S`: `u` and its gradient, `Du`, are continuous on `S`, and `Du`
is the derivative of `u` at interior points. -/
def IsC1On (S : Set R2) (u : R2 → ℂ) (Du : R2 → (R2 →L[ℝ] ℂ)) : Prop :=
  ContinuousOn u S ∧ ContinuousOn Du S ∧ ∀ x ∈ interior S, HasFDerivAt u (Du x) x

/-- `u ∈ BC¹(S)` (Section 2, p. 3): `u ∈ C¹(S)` with `u` and its gradient `Du` bounded on `S`. -/
def IsBC1On (S : Set R2) (u : R2 → ℂ) (Du : R2 → (R2 →L[ℝ] ℂ)) : Prop :=
  IsC1On S u Du ∧ ∃ C, ∀ x ∈ S, ‖u x‖ ≤ C ∧ ‖Du x‖ ≤ C

/-- The closed strip `closure(D^+) \ U_h^+` between `Γ` and `Γ_h` (TSP, Section 2, p. 6). -/
def stripPlus (f : ℝ → ℝ) (h : ℝ) : Set R2 := closure (Dplus f) \ Uplus h

/-- The closed strip `closure(D^-) \ U_h^-` between `Γ_h` and `Γ` (TSP, Section 2, p. 6). -/
def stripMinus (f : ℝ → ℝ) (h : ℝ) : Set R2 := closure (Dminus f) \ Uminus h

/-- The Helmholtz equation `Δv + k²v = 0` at every point of `G`. -/
def IsHelmholtzOn (G : Set R2) (k : ℝ) (v : R2 → ℂ) : Prop :=
  ∀ x ∈ G, Laplacian.laplacian v x + ((k : ℂ) ^ 2) * v x = 0

/-! ### Radiation conditions (Definition 2.2, p. 5) -/

/-- Definition 2.2: `v ∈ UPRC(G, k)`: `v` solves the Helmholtz equation in `G`, and for some
`h` and `φ ∈ L^∞(Γ_h)`, `U_h^+ ⊆ G` and `v(x) = 2 ∫_{Γ_h} ∂Φ_k(x,y)/∂y₂ φ(y) ds(y)` on `U_h^+`. -/
def IsUPRC (G : Set R2) (k : ℝ) (v : R2 → ℂ) : Prop :=
  IsHelmholtzOn G k v ∧
    ∃ (h : ℝ) (φ : ℝ → ℂ), MemLp φ ⊤ volume ∧ Uplus h ⊆ G ∧
      ∀ x ∈ Uplus h, v x = 2 * ∫ t, dPhi_dy2 k x (pt t h) * φ t

/-- Definition 2.2: `v ∈ DPRC(G, k)`: as `IsUPRC` with `θ = -1` and `U_h^-` in place of `U_h^+`. -/
def IsDPRC (G : Set R2) (k : ℝ) (v : R2 → ℂ) : Prop :=
  IsHelmholtzOn G k v ∧
    ∃ (h : ℝ) (φ : ℝ → ℂ), MemLp φ ⊤ volume ∧ Uminus h ⊆ G ∧
      ∀ x ∈ Uminus h, v x = -2 * ∫ t, dPhi_dy2 k x (pt t h) * φ t

/-! ### The Transmission Scattering Problem (Section 2, p. 6) -/

/-- Section 2, p. 6: `(u₊, u₋)` solves the TSP for the scatterer `(Γ, k₋, k₊, μ)` with data
`(g₁, g₂)` (given as functions of `s`, the point `(s, f(s))` of `Γ`):
`u₊ ∈ C²(D^+) ∩ BC¹(closure(D^+) \ U_{h₊}^+)` for some `h₊ > f^+` and
`u₋ ∈ C²(D^-) ∩ BC¹(closure(D^-) \ U_{h₋}^-)` for some `h₋ < f^-`, with gradients `Du₊, Du₋`
continuous up to `Γ`, and (i) `Δu_± + k_±² u_± = 0` in `D^±`; (ii) `u₊ - u₋ = g₁` and
`∂_n u₊ - μ ∂_n u₋ = g₂` on `Γ`; (iii) `sup_{D^±} |x₂|^β |u_±(x)| < ∞` for some `β ∈ ℝ`;
(iv) `u₊ ∈ UPRC(D^+, k₊)` and `u₋ ∈ DPRC(D^-, k₋)`. The data's Hölder class is a hypothesis of
the theorems that use it, not part of this predicate. -/
def IsTSPSolution (f : ℝ → ℝ) (kp km μ : ℝ) (g1 g2 : ℝ → ℂ) (up um : R2 → ℂ) : Prop :=
  ∃ (hp hm : ℝ) (Dup Dum : R2 → (R2 →L[ℝ] ℂ)),
    fsup f < hp ∧ hm < finf f ∧
    ContDiffOn ℝ 2 up (Dplus f) ∧ ContDiffOn ℝ 2 um (Dminus f) ∧
    IsBC1On (stripPlus f hp) up Dup ∧ IsBC1On (stripMinus f hm) um Dum ∧
    IsHelmholtzOn (Dplus f) kp up ∧ IsHelmholtzOn (Dminus f) km um ∧
    (∀ s, up (gpt f s) - um (gpt f s) = g1 s) ∧
    (∀ s, Dup (gpt f s) (normal f s) - (μ : ℂ) * Dum (gpt f s) (normal f s) = g2 s) ∧
    (∃ β C : ℝ, (∀ x ∈ Dplus f, |x 1| ^ β * ‖up x‖ ≤ C) ∧
      ∀ x ∈ Dminus f, |x 1| ^ β * ‖um x‖ ≤ C) ∧
    IsUPRC (Dplus f) kp up ∧ IsDPRC (Dminus f) km um

/-- The scatterer conditions of Theorems 3.3, 4.2 and 4.3: `k₊, k₋, μ > 0`,
`(μ - 1)(k₊² - k₋² μ) ≥ 0` and `k₊² ≠ k₋² μ`. -/
def ParamCond (kp km μ : ℝ) : Prop :=
  0 < kp ∧ 0 < km ∧ 0 < μ ∧ 0 ≤ (μ - 1) * (kp ^ 2 - km ^ 2 * μ) ∧ kp ^ 2 ≠ km ^ 2 * μ

/-- Problem (2.1): the TSP data generated by an incident field `uⁱ`:
`g₁ = -uⁱ|_Γ`, `g₂ = -∂_n uⁱ|_Γ` (so that `u₊ + uⁱ = u₋`, `∂_n u₊ + ∂_n uⁱ = μ ∂_n u₋`). -/
def incData (f : ℝ → ℝ) (ui : R2 → ℂ) : (ℝ → ℂ) × (ℝ → ℂ) :=
  (fun s => -ui (gpt f s), fun s => -(fderiv ℝ ui (gpt f s) (normal f s)))

/-- The incident point source `Φ_k(·, z)` (Sections 5 and 6). -/
def pointSource (k : ℝ) (z : R2) : R2 → ℂ := fun x => Phi k x z

/-- The incident hypersingular point source `∇_x Φ_k(x, z) · ν` (Theorem 5.3, p. 21). -/
def dipoleSource (k : ℝ) (z ν : R2) : R2 → ℂ := fun x => fderiv ℝ (fun x' => Phi k x' z) x ν

/-! ### Impedance Green's functions and the integral operators (eq. (2.8); Section 4) -/

/-- The reflection `y'_a = (y₁, 2a - y₂)` of `y` in the line `Γ_a` (Section 2, p. 7). -/
def refl (a : ℝ) (y : R2) : R2 := pt (y 0) (2 * a - y 1)

/-- Section 2, p. 7: `P_k^±(z) = (|z| e^{ik|z|}/π) ∫₀^∞ t^{-1/2} e^{-k|z|t} [|z| ± z₂(1+it)] /
(√(t-2i) [|z|t - i(|z| ± z₂)]²) dt`, with `σ = 1` for `+` and `σ = -1` for `-`, and the principal
square root (`-π/2 < arg √(t-2i) < 0`). -/
def Pimp (k σ : ℝ) (z : R2) : ℂ :=
  ((‖z‖ : ℂ) * Complex.exp (Complex.I * k * ‖z‖) / Real.pi) *
    ∫ t in Set.Ioi (0 : ℝ),
      ((t ^ (-(1 / 2 : ℝ)) * Real.exp (-k * ‖z‖ * t) : ℝ) : ℂ) *
        ((‖z‖ : ℂ) + σ * z 1 * (1 + Complex.I * t)) /
        ((((t : ℂ) - 2 * Complex.I) ^ (1 / 2 : ℂ)) *
          ((‖z‖ : ℂ) * t - Complex.I * (‖z‖ + σ * z 1)) ^ 2)

/-- Eq. (2.8): the impedance Green's function of the half plane `U_a^±`,
`G_k^{±(I)}(x,y;a) = Φ_k(x,y) + Φ_k(x,y'_a) + P_k^±(x - y'_a)` (`σ = ±1`). -/
def Gimp (k a σ : ℝ) (x y : R2) : ℂ :=
  Phi k x y + Phi k x (refl a y) + Pimp k σ (x - refl a y)

/-- The kernel `K(x, y)` at `x = (s, f(s))`, `y = (t, f(t))`. -/
def kerGam (f : ℝ → ℝ) (K : R2 → R2 → ℂ) (s t : ℝ) : ℂ := K (gpt f s) (gpt f t)

/-- The kernel `∂K(x,y)/∂n'(y)` (`n' = normalUp`, into `D^+`) at `x = (s, f(s))`, `y = (t, f(t))`. -/
def dnyGam (f : ℝ → ℝ) (K : R2 → R2 → ℂ) (s t : ℝ) : ℂ :=
  fderiv ℝ (fun y => K (gpt f s) y) (gpt f t) (normalUp f t)

/-- The kernel `∂K(x,y)/∂n'(x)` (`n' = normalUp`, into `D^+`) at `x = (s, f(s))`, `y = (t, f(t))`. -/
def dnxGam (f : ℝ → ℝ) (K : R2 → R2 → ℂ) (s t : ℝ) : ℂ :=
  fderiv ℝ (fun x => K x (gpt f t)) (gpt f s) (normalUp f s)

/-- The kernel `∂²K(x,y)/∂n'(x)∂n'(y)` (`n' = normalUp`, into `D^+`) at `x = (s, f(s))`, `y = (t, f(t))`. -/
def dnxdnyGam (f : ℝ → ℝ) (K : R2 → R2 → ℂ) (s t : ℝ) : ℂ :=
  fderiv ℝ (fun x => fderiv ℝ (fun y => K x y) (gpt f t) (normalUp f t)) (gpt f s) (normalUp f s)

/-- The boundary integral `∫_Γ k(x, y) φ(y) ds(y)` at `x = (s, f(s))`. -/
def bdryInt (f : ℝ → ℝ) (ker : ℝ → ℝ → ℂ) (φ : ℝ → ℂ) (s : ℝ) : ℂ :=
  ∫ t, ker s t * φ t * (arcDen f t : ℂ)

/-- Section 4, p. 13: the single-layer potential `(𝒮_{k,a}^± ψ)(x) = ∫_Γ G_k^{±(I)}(x,y;a) ψ(y) ds(y)`
(`σ = ±1`). -/
def singleLayer (f : ℝ → ℝ) (k a σ : ℝ) (ψ : ℝ → ℂ) (x : R2) : ℂ :=
  ∫ t, Gimp k a σ x (gpt f t) * ψ t * (arcDen f t : ℂ)

/-- Section 4, p. 13: the double-layer potential
`(𝒟_{k,a}^± φ)(x) = ∫_Γ ∂G_k^{±(I)}(x,y;a)/∂n'(y) φ(y) ds(y)` (`σ = ±1`), with the normal
`n' = normalUp` pointing into `D^+` (see `normalUp`). -/
def doubleLayer (f : ℝ → ℝ) (k a σ : ℝ) (φ : ℝ → ℂ) (x : R2) : ℂ :=
  ∫ t, fderiv ℝ (fun y => Gimp k a σ x y) (gpt f t) (normalUp f t) * φ t * (arcDen f t : ℂ)

/-- Section 4, p. 14 (and eq. (4.14), p. 16): the operator
`M = [[K⁺ - μ⁻¹K⁻ + (1+μ)(2μ)⁻¹ I, S⁺ - μ⁻¹S⁻], [T⁻ - T⁺, K'⁻ - K'⁺ + I]]` applied to `χ = (φ, ψ)`,
where `⁺` stands for `k₊` and `G_{k₊}^{+(I)}(·,·;h₋)`, and `⁻` for `k₋` and
`G_{k₋}^{-(I)}(·,·;h₊)`. `S, K, K'` have kernels `G`, `∂G/∂n'(y)`, `∂G/∂n'(x)` with the normal
`n' = normalUp` into `D^+`; the difference
`T⁻ - T⁺` is the integral operator with kernel `∂²(G⁻ - G⁺)/∂n'(x)∂n'(y)`, the form in which it acts
on `[BC(Γ)]²` ([DTS03, Section 4]). -/
def Mop (f : ℝ → ℝ) (kp km μ hm hp : ℝ) (φ ψ : ℝ → ℂ) : (ℝ → ℂ) × (ℝ → ℂ) :=
  let Gp : R2 → R2 → ℂ := Gimp kp hm 1
  let Gm : R2 → R2 → ℂ := Gimp km hp (-1)
  (fun s => bdryInt f (dnyGam f Gp) φ s - (μ : ℂ)⁻¹ * bdryInt f (dnyGam f Gm) φ s +
      (((1 + μ) / (2 * μ) : ℝ) : ℂ) * φ s +
      bdryInt f (kerGam f Gp) ψ s - (μ : ℂ)⁻¹ * bdryInt f (kerGam f Gm) ψ s,
   fun s => bdryInt f (dnxdnyGam f (fun x y => Gm x y - Gp x y)) φ s +
      bdryInt f (dnxGam f Gm) ψ s - bdryInt f (dnxGam f Gp) ψ s + ψ s)

/-! ### Sobolev quantities and domains (Sections 5 and 6) -/

/-- `g` is the weak derivative of `u` in direction `v` on the open set `U`:
`∫_U u ∂_v φ = -∫_U g φ` for every `φ ∈ C_c^∞(U)`. -/
def IsWeakDeriv (U : Set R2) (u : R2 → ℂ) (v : R2) (g : R2 → ℂ) : Prop :=
  ∀ φ : R2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
    ∫ x in U, u x * ((fderiv ℝ φ x v : ℝ) : ℂ) = -∫ x in U, g x * (φ x : ℂ)

/-- Lemma 5.1, p. 17: `u ∈ W^{2,p}(U)`: `u`, its weak first derivatives and its weak second
derivatives belong to `L^p(U)`. -/
def MemW2p (U : Set R2) (p : ENNReal) (u : R2 → ℂ) : Prop :=
  MemLp u p (volume.restrict U) ∧
    ∀ i : Fin 2, ∃ gi : R2 → ℂ, MemLp gi p (volume.restrict U) ∧
      IsWeakDeriv U u (EuclideanSpace.single i 1) gi ∧
      ∀ j : Fin 2, ∃ gij : R2 → ℂ, MemLp gij p (volume.restrict U) ∧
        IsWeakDeriv U gi (EuclideanSpace.single j 1) gij

/-- `‖w‖_{H¹(D)} = (∫_D |w|² + |∂₁w|² + |∂₂w|²)^{1/2}` for `w` continuously differentiable on the
open set `D` (Section 5), with value `∞` when the integral diverges. -/
def h1Norm (D : Set R2) (w : R2 → ℂ) : ENNReal :=
  (∫⁻ x in D, ‖w x‖ₑ ^ 2 + ‖fderiv ℝ w x (EuclideanSpace.single 0 1)‖ₑ ^ 2 +
      ‖fderiv ℝ w x (EuclideanSpace.single 1 1)‖ₑ ^ 2) ^ (1 / 2 : ℝ)

/-- `‖w‖_{L²(D)}` (Theorem 5.3). -/
def l2Norm (D : Set R2) (w : R2 → ℂ) : ENNReal := eLpNorm w 2 (volume.restrict D)

/-- Theorems 5.2 and 6.1: `D` is a bounded `C^{2,λ}` domain: a bounded connected open set which
near each boundary point is, in suitable rotated (or reflected) coordinates centred at that point,
the region below the graph of a `C^{2,λ}` function. -/
def IsC2LambdaDomain (lam : ℝ) (D : Set R2) : Prop :=
  IsOpen D ∧ IsConnected D ∧ Bornology.IsBounded D ∧
    ∀ p ∈ frontier D, ∃ (Q : R2 ≃ₗᵢ[ℝ] R2) (r : ℝ) (g : ℝ → ℝ), 0 < r ∧ IsC2Lambda lam g ∧
      ∀ x ∈ Metric.ball p r, (x ∈ D ↔ (Q (x - p)) 1 < g ((Q (x - p)) 0))

/-- `ν` is the outward unit normal of `D` at the boundary point `y`: points near `y` strictly on
the side of `-ν` (in a cone of any opening below `π`) lie in `D`, those on the side of `ν` do not. -/
def IsOutwardNormal (D : Set R2) (y ν : R2) : Prop :=
  ‖ν‖ = 1 ∧ ∀ ε > (0 : ℝ), ∃ r > (0 : ℝ), ∀ z ∈ Metric.ball y r, z ≠ y →
    (@inner ℝ R2 _ (z - y) ν ≤ -ε * ‖z - y‖ → z ∈ D) ∧
    (ε * ‖z - y‖ ≤ @inner ℝ R2 _ (z - y) ν → z ∉ D)

open Classical in
/-- The outward unit normal `n(y)` of `D` at `y ∈ ∂D` (Theorem 5.3, p. 21). -/
def outwardNormal (D : Set R2) (y : R2) : R2 :=
  if h : ∃ ν, IsOutwardNormal D y ν then h.choose else 0

/-- Theorem 5.3, p. 21: `v_j(x) = 2μ(1-μ)/(μ+1)² ∫_{∂D₀} ∂Φ₀(x,y)/∂n(y)
(∇_xΦ₀(y,x_j) + ∇_xΦ₀(y,y_j))·n(x₀) ds(y)`, with `ds` the arc length (one-dimensional Hausdorff
measure) on `∂D₀` and `n(y)` the outward normal of `D₀`. -/
def vCorr (μ : ℝ) (D0 : Set R2) (n0 xj yj x : R2) : ℂ :=
  ((2 * μ * (1 - μ) / (μ + 1) ^ 2 : ℝ) : ℂ) *
    ∫ y, fderiv ℝ (fun y' => Phi 0 x y') y (outwardNormal D0 y) *
        (dipoleSource 0 xj n0 y + dipoleSource 0 yj n0 y)
      ∂((Measure.hausdorffMeasure 1 : Measure R2).restrict (frontier D0))

/-- Section 6, p. 22: the measurement segment `Γ_{c,d} = {(x₁, c) : |x₁| ≤ d}`. -/
def measSeg (c d : ℝ) : Set R2 := {x | x 1 = c ∧ |x 0| ≤ d}

end RoughSurfaceScattering


