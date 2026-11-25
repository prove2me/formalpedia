-- Prove2me | Definitions.Def_Arxiv2210_02565_Basic
-- name    : Arxiv2210_02565_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T12:46:43.473559+00:00
-- url     : https://prove2.me/theorems/aaed1b91-3bf9-5448-a6e1-662f643661b3
-- title:
--   Fields, Green function, planewave source field, Müller formulation and image/Mie construction for layered-media scattering
-- statement:
--   Objects of Sections II-IV and VI and Appendix A of Arrieta and Pérez-Arancibia (2022).
--
--   1. **Space and fields.** Points of $\mathbb{R}^3$ are $\mathbf r=(x,y,z)$; time-harmonic fields (time dependence $e^{-i\omega t}$) take values in $\mathbb{C}^3$. $\partial_i$, $\nabla$ and $\nabla\times$ are the usual partial derivative, gradient and curl of complex fields, and $\times$ is the cross product on $\mathbb{C}^3$. $\hat{\mathbf z}=(0,0,1)$ is the normal of the plane $\Sigma=\{z=0\}$.
--   2. **Green function (eq. 9).** $G(\mathbf r,\mathbf r')=\dfrac{e^{ik|\mathbf r-\mathbf r'|}}{4\pi|\mathbf r-\mathbf r'|}$ for a wavenumber $k\in\mathbb{C}$.
--   3. **Planewave source field (Section III).** Data: $\omega$, $\epsilon_1,\mu_1,\epsilon_2,\mu_2$, real $k_{1y},k_{1z}$ with wave vector $\mathbf k=(0,k_{1y},-k_{1z})$, and $\mathbf p\in\mathbb{C}^3$. Put $k_{2y}=k_{1y}$ and $k_{2z}=\sqrt{\omega^2\mu_2\epsilon_2-k_{1y}^2}$ with $\operatorname{Im}k_{2z}\ge0$. The Fresnel coefficients are
--   $$R^{\rm TE}=\frac{\mu_2k_{1z}-\mu_1k_{2z}}{\mu_2k_{1z}+\mu_1k_{2z}},\quad R^{\rm TM}=\frac{\epsilon_2k_{1z}-\epsilon_1k_{2z}}{\epsilon_2k_{1z}+\epsilon_1k_{2z}},\quad T^{\rm TE}=\frac{2\mu_2k_{1z}}{\mu_2k_{1z}+\mu_1k_{2z}},\quad T^{\rm TM}=\frac{2\epsilon_2k_{1z}}{\epsilon_2k_{1z}+\epsilon_1k_{2z}},$$
--   and the amplitudes are $E_0=-p_zk_{1y}-p_yk_{1z}$ and $H_0=k_1^2p_x/(\omega\mu_1)$ with $k_1^2=\omega^2\mu_1\epsilon_1$. The transverse components are $E_x=E_0(e^{i(k_{1y}y-k_{1z}z)}+R^{\rm TE}e^{i(k_{1y}y+k_{1z}z)})$ and $H_x=H_0(e^{i(k_{1y}y-k_{1z}z)}+R^{\rm TM}e^{i(k_{1y}y+k_{1z}z)})$ for incident plus reflected, and $E_x=E_0T^{\rm TE}e^{i(k_{2y}y-k_{2z}z)}$, $H_x=H_0T^{\rm TM}e^{i(k_{2y}y-k_{2z}z)}$ for transmitted. The fields are
--   $$\mathbf E=E_x\hat{\mathbf x}-\tfrac{1}{i\omega\epsilon}\partial_zH_x\,\hat{\mathbf y}+\tfrac{1}{i\omega\epsilon}\partial_yH_x\,\hat{\mathbf z},\qquad \mathbf H=H_x\hat{\mathbf x}+\tfrac{1}{i\omega\mu}\partial_zE_x\,\hat{\mathbf y}-\tfrac{1}{i\omega\mu}\partial_yE_x\,\hat{\mathbf z},$$
--   with $(\epsilon,\mu)=(\epsilon_1,\mu_1)$ for the expression used in $\Omega_1$ (incident plus reflected) and $(\epsilon_2,\mu_2)$ for the expression used in $\Omega_2$ (transmitted), as in eq. (7). The source currents of eq. (5) are $\mathbf M^{\rm src}=\hat{\mathbf n}\times(\mathbf E^{\rm src}|_+-\mathbf E^{\rm src}|_-)$ and $\mathbf J^{\rm src}=\hat{\mathbf n}\times(\mathbf H^{\rm src}|_+-\mathbf H^{\rm src}|_-)$, where the $+$ side is $\Omega_1$.
--   4. **Müller formulation (Section IV).** For tangential currents $\mathbf u,\mathbf v$ and potentials $\mathcal S_j,\mathcal D_j$: $\mathbf E_j=k_j^2\mathcal S_j\mathbf v+i\omega\mu_j\mathcal D_j\mathbf u$ and $\mathbf H_j=k_j^2\mathcal S_j\mathbf u-i\omega\epsilon_j\mathcal D_j\mathbf v$ (eq. 13). Their traces are $\hat{\mathbf n}\times\mathbf E_j|_\pm=k_j^2(\hat{\mathbf n}\times\mathcal S_j\mathbf v)|_\pm+i\omega\mu_j(\hat{\mathbf n}\times\mathcal D_j\mathbf u)|_\pm$, and similarly for $\mathbf H_j$. The left-hand side of the integral equation (18)-(19) is
--   $$\frac{i\omega}{2}\begin{bmatrix}-(\mu_1+\mu_2)\mathbf u\\(\epsilon_1+\epsilon_2)\mathbf v\end{bmatrix}+\begin{bmatrix}i\omega(\mu_2\mathcal K_2-\mu_1\mathcal K_1)&k_2^2\mathcal T_2-k_1^2\mathcal T_1\\k_2^2\mathcal T_2-k_1^2\mathcal T_1&-i\omega(\epsilon_2\mathcal K_2-\epsilon_1\mathcal K_1)\end{bmatrix}\begin{bmatrix}\mathbf u\\\mathbf v\end{bmatrix}.$$
--   5. **Hemispherical bump (Appendix A).** For $k>0$, amplitude $E_0$ and grazing angle $\alpha$: $\mathbf E^{\rm inc}_\alpha(\mathbf r)=E_0e^{ik(y\cos\alpha-z\sin\alpha)}\,\mathbf q$ with $\mathbf q=\hat{\mathbf x}$ (TE) or $\mathbf q=\hat{\mathbf y}\sin\alpha+\hat{\mathbf z}\cos\alpha$ (TM). The image field is $\widetilde{\mathbf E}^{\rm inc}=-\mathbf E^{\rm inc}_{-\alpha}$ (TE) or $\mathbf E^{\rm inc}_{-\alpha}$ (TM). For an incident field $\mathbf E^{\rm inc}$, the Mie field $\mathbf E^{\rm Mie}$ of the PEC sphere $|\mathbf r|\le a$ is the field that is $C^2$ in $|\mathbf r|>a$, is continuous up to $|\mathbf r|=a$, and satisfies $\nabla\times\nabla\times\mathbf E^{\rm Mie}=k^2\mathbf E^{\rm Mie}$, $\mathbf r\times(\mathbf E^{\rm inc}+\mathbf E^{\rm Mie})=\mathbf 0$ on $|\mathbf r|=a$, and $|\mathbf r|\,\big((\nabla\times\mathbf E^{\rm Mie})\times\hat{\mathbf r}-ik\mathbf E^{\rm Mie}\big)\to0$ uniformly as $|\mathbf r|\to\infty$. The total field is $\mathbf E^{\rm tot}=\mathbf E^{\rm inc}_\alpha+\mathbf E^{\rm Mie}+\widetilde{\mathbf E}^{\rm inc}+\widetilde{\mathbf E}^{\rm Mie}$.
--
--   **Formalization Note** The integrals over the unbounded interface $\Gamma$ are only conditionally convergent (Section IV) and the paper gives no summation rule for them. So $\mathcal S_j,\mathcal D_j,\mathcal T_j,\mathcal K_j$, the curl acting on the represented fields, and the one-sided traces are linear maps on abstract complex vector spaces of currents and fields. The Mie field is defined as the scattered field with the properties listed above (junk value $0$ if none existed), not as the series. Its existence and uniqueness are classical. The radiation condition is written in terms of $\mathbf E$ alone, which is eq. (3) after substituting $\mathbf H=\nabla\times\mathbf E/(i\omega\mu)$. The Green function takes the junk value $0$ at $\mathbf r=\mathbf r'$, a point no statement uses.
-- source:
--   Arrieta and Pérez-Arancibia, Windowed Green Function MoM for Second-Kind Surface Integral Equation Formulations of Layered Media Electromagnetic Scattering Problems, arXiv:2210.02565v1 (2022), Sections II, III (eqs. (2)-(7)), IV (eqs. (11)-(19)), VI (eq. (9) and the I^(3) estimate) and Appendix A, PDF pp. 2-5, 11

import Mathlib

/-!
R. Arrieta and C. Pérez-Arancibia, *Windowed Green Function MoM for Second-Kind Surface Integral
Equation Formulations of Layered Media Electromagnetic Scattering Problems*, arXiv:2210.02565v1
(2022): the differential operators and Green function of Sections II-IV and VI, the planewave
source field of Section III, the indirect Müller representation and second-kind integral equation
of Section IV, and the image/Mie construction of Appendix A.
-/

open Filter Topology

noncomputable section

namespace Arxiv2210_02565

/-- Physical space `ℝ³` (Section II); the point `r` has coordinates `(x, y, z) = (r 0, r 1, r 2)`. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- Complex vectors `ℂ³`, the values of the time-harmonic fields (Section II). -/
abbrev CVec := Fin 3 → ℂ

/-- A point (or real vector) of space viewed as a complex vector. -/
def toC (r : Space) : CVec := fun i => ((r i : ℝ) : ℂ)

/-- The unit vector `ẑ`, the normal `n̂` on the planar surface `Σ = {z = 0}` (Sections II-III). -/
def zhat : CVec := ![0, 0, 1]

/-- The partial derivative `∂f/∂x_i` of a complex scalar field at `r`. -/
def pd (i : Fin 3) (f : Space → ℂ) (r : Space) : ℂ :=
  fderiv ℝ f r (EuclideanSpace.single i 1)

/-- The gradient `∇f` of a complex scalar field (Section VI). -/
def grad (f : Space → ℂ) (r : Space) : CVec := ![pd 0 f r, pd 1 f r, pd 2 f r]

/-- The curl `∇ × F` of a complex vector field (eq. (2)). -/
def curl (F : Space → CVec) (r : Space) : CVec :=
  ![pd 1 (fun q => F q 2) r - pd 2 (fun q => F q 1) r,
    pd 2 (fun q => F q 0) r - pd 0 (fun q => F q 2) r,
    pd 0 (fun q => F q 1) r - pd 1 (fun q => F q 0) r]

/-- Eq. (9): the free-space Helmholtz Green function `G(r, r') = e^{ik|r-r'|} / (4π|r-r'|)`
(junk value `0` at `r = r'`, which no statement uses). -/
def greenFn (k : ℂ) (r r' : Space) : ℂ :=
  Complex.exp (Complex.I * k * (‖r - r'‖ : ℂ)) / (4 * Real.pi * (‖r - r'‖ : ℂ))

/-! ### Section III: the planewave source field -/

/-- Section III: the data of a planewave incident from `D₁ = {z > 0}` on the flat interface
`Σ = {z = 0}`: the angular frequency `ω`, the permittivities and permeabilities `ε_j, μ_j` of
`D₁` and `D₂ = {z < 0}`, the components of the wave vector `k = (0, k_{1y}, -k_{1z})` and the
vector `p` of eq. (6). -/
structure PlanewaveSetup where
  ω : ℝ
  ε1 : ℂ
  μ1 : ℂ
  ε2 : ℂ
  μ2 : ℂ
  k1y : ℝ
  k1z : ℝ
  p : CVec

namespace PlanewaveSetup

variable (s : PlanewaveSetup)

/-- Section III: `k_{2z} = √(k_2² - k_{2y}²)` with `k_2² = ω²μ₂ε₂`, `k_{2y} = k_{1y}`, and the
complex square root chosen so that `Im k_{2z} ≥ 0` (the principal root, negated if its imaginary
part is negative; for a positive radicand this is the positive root). -/
def k2z : ℂ :=
  let w : ℂ := ((s.ω : ℂ) ^ 2 * s.μ2 * s.ε2 - (s.k1y : ℂ) ^ 2) ^ (1 / 2 : ℂ)
  if 0 ≤ w.im then w else -w

/-- Section III: the reflection coefficient `R^TE = (μ₂k_{1z} - μ₁k_{2z}) / (μ₂k_{1z} + μ₁k_{2z})`. -/
def RTE : ℂ := (s.μ2 * s.k1z - s.μ1 * s.k2z) / (s.μ2 * s.k1z + s.μ1 * s.k2z)

/-- Section III: the reflection coefficient `R^TM = (ε₂k_{1z} - ε₁k_{2z}) / (ε₂k_{1z} + ε₁k_{2z})`. -/
def RTM : ℂ := (s.ε2 * s.k1z - s.ε1 * s.k2z) / (s.ε2 * s.k1z + s.ε1 * s.k2z)

/-- Section III: the transmission coefficient `T^TE = 2μ₂k_{1z} / (μ₂k_{1z} + μ₁k_{2z})`. -/
def TTE : ℂ := 2 * s.μ2 * s.k1z / (s.μ2 * s.k1z + s.μ1 * s.k2z)

/-- Section III: the transmission coefficient `T^TM = 2ε₂k_{1z} / (ε₂k_{1z} + ε₁k_{2z})`. -/
def TTM : ℂ := 2 * s.ε2 * s.k1z / (s.ε2 * s.k1z + s.ε1 * s.k2z)

/-- Section III: the amplitude `E₀ = -p_z k_{1y} - p_y k_{1z}`. -/
def E0 : ℂ := -s.p 2 * s.k1y - s.p 1 * s.k1z

/-- Section III: the amplitude `H₀ = k₁² p_x / (ωμ₁)`, with `k₁² = ω²μ₁ε₁`. -/
def H0 : ℂ := (s.ω : ℂ) ^ 2 * s.μ1 * s.ε1 / (s.ω * s.μ1) * s.p 0

/-- Section III: the transverse components `E_x^inc + E_x^ref` of the total field in `D₁`,
`E₀ e^{i(k_{1y}y - k_{1z}z)} + E₀ R^TE e^{i(k_{1y}y + k_{1z}z)}`, as a function of `(y, z)`. -/
def Ex1 (y z : ℝ) : ℂ :=
  s.E0 * Complex.exp (Complex.I * (s.k1y * y - s.k1z * z)) +
    s.E0 * s.RTE * Complex.exp (Complex.I * (s.k1y * y + s.k1z * z))

/-- Section III: `H_x^inc + H_x^ref = H₀ e^{i(k_{1y}y - k_{1z}z)} + H₀ R^TM e^{i(k_{1y}y + k_{1z}z)}`. -/
def Hx1 (y z : ℝ) : ℂ :=
  s.H0 * Complex.exp (Complex.I * (s.k1y * y - s.k1z * z)) +
    s.H0 * s.RTM * Complex.exp (Complex.I * (s.k1y * y + s.k1z * z))

/-- Section III: the transmitted transverse component `E_x^trs = E₀ T^TE e^{i(k_{2y}y - k_{2z}z)}`,
`k_{2y} = k_{1y}`. -/
def Ex2 (y z : ℝ) : ℂ := s.E0 * s.TTE * Complex.exp (Complex.I * (s.k1y * y - s.k2z * z))

/-- Section III: the transmitted transverse component `H_x^trs = H₀ T^TM e^{i(k_{2y}y - k_{2z}z)}`. -/
def Hx2 (y z : ℝ) : ℂ := s.H0 * s.TTM * Complex.exp (Complex.I * (s.k1y * y - s.k2z * z))

end PlanewaveSetup

/-- Section III: the `x`-independent electric field retrieved from its transverse components,
`E = E_x x̂ - (1/(iωε)) ∂_z H_x ŷ + (1/(iωε)) ∂_y H_x ẑ`. -/
def fieldE (ω : ℝ) (ε : ℂ) (Ex Hx : ℝ → ℝ → ℂ) (r : Space) : CVec :=
  ![Ex (r 1) (r 2),
    -(1 / (Complex.I * ω * ε)) * deriv (fun z => Hx (r 1) z) (r 2),
    (1 / (Complex.I * ω * ε)) * deriv (fun y => Hx y (r 2)) (r 1)]

/-- Section III: the `x`-independent magnetic field retrieved from its transverse components,
`H = H_x x̂ + (1/(iωμ)) ∂_z E_x ŷ - (1/(iωμ)) ∂_y E_x ẑ`. -/
def fieldH (ω : ℝ) (μ : ℂ) (Ex Hx : ℝ → ℝ → ℂ) (r : Space) : CVec :=
  ![Hx (r 1) (r 2),
    (1 / (Complex.I * ω * μ)) * deriv (fun z => Ex (r 1) z) (r 2),
    -(1 / (Complex.I * ω * μ)) * deriv (fun y => Ex y (r 2)) (r 1)]

/-- Eq. (7), the expression used in `Ω₁`: `E^src = E^inc + E^ref`. -/
def srcE1 (s : PlanewaveSetup) : Space → CVec := fieldE s.ω s.ε1 s.Ex1 s.Hx1

/-- Eq. (7), the expression used in `Ω₂`: `E^src = E^trs`. -/
def srcE2 (s : PlanewaveSetup) : Space → CVec := fieldE s.ω s.ε2 s.Ex2 s.Hx2

/-- Eq. (7), the expression used in `Ω₁`: `H^src = H^inc + H^ref`. -/
def srcH1 (s : PlanewaveSetup) : Space → CVec := fieldH s.ω s.μ1 s.Ex1 s.Hx1

/-- Eq. (7), the expression used in `Ω₂`: `H^src = H^trs`. -/
def srcH2 (s : PlanewaveSetup) : Space → CVec := fieldH s.ω s.μ2 s.Ex2 s.Hx2

/-- Eq. (5a) for the planewave source field (7): `M^src = n̂ × (E^src|₊ - E^src|₋)`, where the
`+` side is `Ω₁` and the `-` side is `Ω₂`; both expressions in (7) are smooth on all of space,
so the one-sided limits are their values at `r`. -/
def srcCurrentM (s : PlanewaveSetup) (n : CVec) (r : Space) : CVec :=
  crossProduct n (srcE1 s r - srcE2 s r)

/-- Eq. (5b) for the planewave source field (7): `J^src = n̂ × (H^src|₊ - H^src|₋)`. -/
def srcCurrentJ (s : PlanewaveSetup) (n : CVec) (r : Space) : CVec :=
  crossProduct n (srcH1 s r - srcH2 s r)

/-! ### Section IV: the indirect Müller formulation

The surface integrals over the unbounded interface `Γ` are only conditionally convergent
(Section IV), so the potentials `S_j, D_j` and the boundary operators `T_j, K_j` enter as linear
maps on a space `V` of tangential surface currents (values in a space `W` of fields), and the
one-sided traces `n̂ × (S_j φ)|_±`, `n̂ × (D_j φ)|_±` as linear maps `V → V`. -/

section Muller

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Eq. (13a): `E_j = k_j² S_j v + iωμ_j D_j u`. -/
def mullerE (ω : ℝ) (μ k : ℂ) (S D : V →ₗ[ℂ] W) (u v : V) : W :=
  k ^ 2 • S v + (Complex.I * ω * μ) • D u

/-- Eq. (13b): `H_j = k_j² S_j u - iωε_j D_j v`. -/
def mullerH (ω : ℝ) (ε k : ℂ) (S D : V →ₗ[ℂ] W) (u v : V) : W :=
  k ^ 2 • S u - (Complex.I * ω * ε) • D v

/-- Eq. (17a) before using (14): the trace `n̂ × E_j|_±` of (13a), i.e.
`k_j² (n̂ × S_j v)|_± + iωμ_j (n̂ × D_j u)|_±`, given the trace maps
`trS φ = n̂ × (S_j φ)|_±` and `trD φ = n̂ × (D_j φ)|_±` of one side. -/
def mullerTraceE (ω : ℝ) (μ k : ℂ) (trS trD : V →ₗ[ℂ] V) (u v : V) : V :=
  k ^ 2 • trS v + (Complex.I * ω * μ) • trD u

/-- Eq. (17b) before using (14): the trace `n̂ × H_j|_±` of (13b),
`k_j² (n̂ × S_j u)|_± - iωε_j (n̂ × D_j v)|_±`. -/
def mullerTraceH (ω : ℝ) (ε k : ℂ) (trS trD : V →ₗ[ℂ] V) (u v : V) : V :=
  k ^ 2 • trS u - (Complex.I * ω * ε) • trD v

/-- Eqs. (18)-(19): the left-hand side of the second-kind integral equation,
`(iω/2) [-(μ₁+μ₂) u, (ε₁+ε₂) v] + 𝖳 [u, v]` with
`𝖳 = [[iω(μ₂K₂ - μ₁K₁), k₂²T₂ - k₁²T₁], [k₂²T₂ - k₁²T₁, -iω(ε₂K₂ - ε₁K₁)]]`. -/
def mullerSIE (ω : ℝ) (ε1 μ1 k1 ε2 μ2 k2 : ℂ) (T1 K1 T2 K2 : V →ₗ[ℂ] V) (u v : V) : V × V :=
  ((Complex.I * ω / 2) • ((-(μ1 + μ2)) • u) +
      ((Complex.I * ω) • (μ2 • K2 u - μ1 • K1 u) + (k2 ^ 2 • T2 v - k1 ^ 2 • T1 v)),
    (Complex.I * ω / 2) • ((ε1 + ε2) • v) +
      ((k2 ^ 2 • T2 u - k1 ^ 2 • T1 u) + (-(Complex.I * ω)) • (ε2 • K2 v - ε1 • K1 v)))

end Muller

/-! ### Appendix A: the hemispherical bump -/

/-- Appendix A: the polarization of `E^inc_α`: `x̂` if TE polarized (`te = true`), and
`ŷ sin α + ẑ cos α` if TM polarized (`te = false`). -/
def bumpPol (te : Bool) (α : ℝ) : CVec :=
  if te then ![1, 0, 0] else ![0, (Real.sin α : ℂ), (Real.cos α : ℂ)]

/-- Appendix A: the incident planewave with grazing angle `α`,
`E^inc_α(r) = E₀ e^{ik(y cos α - z sin α)} p_α`. -/
def incAlpha (k : ℝ) (E0 : ℂ) (te : Bool) (α : ℝ) (r : Space) : CVec :=
  (E0 * Complex.exp (Complex.I * k * (r 1 * Real.cos α - r 2 * Real.sin α))) • bumpPol te α

/-- Appendix A: the image incident field `Ẽ^inc = -E^inc_{-α}` (TE) or `E^inc_{-α}` (TM). -/
def imageInc (k : ℝ) (E0 : ℂ) (te : Bool) (α : ℝ) (r : Space) : CVec :=
  (if te then (-1 : ℂ) else 1) • incAlpha k E0 te (-α) r

/-- Appendix A (with eqs. (2)-(3)): `E^s` is a field scattered by the PEC sphere `|r| ≤ a`
(centred at the origin) under the incident field `E^inc`: `E^s` is `C²` in `|r| > a` and
continuous up to `|r| = a`, solves `∇ × ∇ × E^s = k² E^s` there (Maxwell's equations with
`H^s = ∇ × E^s / (iωμ)`), satisfies the PEC condition `n̂ × (E^inc + E^s) = 0` on `|r| = a`, and
the Silver-Müller radiation condition `|r| ((∇ × E^s) × r̂ - ik E^s) → 0` as `|r| → ∞`,
uniformly in all directions. -/
def IsPECSphereScattered (k a : ℝ) (Einc Es : Space → CVec) : Prop :=
  ContDiffOn ℝ 2 Es {r | a < ‖r‖} ∧ ContinuousOn Es {r | a ≤ ‖r‖} ∧
    (∀ r : Space, a < ‖r‖ → curl (curl Es) r = ((k : ℂ) ^ 2) • Es r) ∧
    (∀ r : Space, ‖r‖ = a → crossProduct (toC r) (Einc r + Es r) = 0) ∧
    Tendsto (fun r : Space => ((‖r‖ : ℝ) : ℂ) •
        (crossProduct (curl Es r) (toC (‖r‖⁻¹ • r)) - (Complex.I * k) • Es r))
      (Bornology.cobounded Space) (𝓝 0)

open Classical in
/-- Appendix A: the Mie solution `E^Mie` of scattering of `E^inc` by the entire PEC sphere of
radius `a` centred at the origin, as the scattered field characterised in
`IsPECSphereScattered` (junk value `0` if no such field exists). -/
def mieField (k a : ℝ) (Einc : Space → CVec) : Space → CVec :=
  if h : ∃ Es, IsPECSphereScattered k a Einc Es then h.choose else 0

/-- Appendix A: the image-method total field
`E^tot = E^inc_α + E^Mie + Ẽ^inc + Ẽ^Mie` for the hemispherical PEC bump of radius `a` on the PEC
half-space `{z < 0}`. -/
def bumpTotalField (k a : ℝ) (E0 : ℂ) (te : Bool) (α : ℝ) : Space → CVec :=
  incAlpha k E0 te α + mieField k a (incAlpha k E0 te α) + imageInc k E0 te α +
    mieField k a (imageInc k E0 te α)

end Arxiv2210_02565


