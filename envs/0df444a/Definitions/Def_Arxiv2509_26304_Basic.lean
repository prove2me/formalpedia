-- Prove2me | Definitions.Def_Arxiv2509_26304_Basic
-- name    : Arxiv2509_26304_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-26T13:06:01.384702+00:00
-- url     : https://prove2.me/theorems/f8c9aa8d-9bdf-47c7-be87-93aa6ac17538
-- title:
--   Two-dimensional TM scattering: Helmholtz equation, far-field amplitude, scattering cross section, trivial wall structure
-- statement:
--   Objects of Section 2 (eqs. (1)-(9)), Section 3 and Section 4.3 of Helsing and Karlsson (2025), in the cross-section plane $z=0$, with points $\boldsymbol\rho=(x,y)\in\mathbb{R}^2$, $\rho=|\boldsymbol\rho|$ and azimuthal angle $\theta$ measured from the $x$-axis.
--
--   1. **Helmholtz equation (eq. 2).** $\nabla^2u=\partial_x^2u+\partial_y^2u$. A field $u:\mathbb{R}^2\to\mathbb{C}$ solves $(\nabla^2+k^2)u=0$ on a set $U$ if it is twice continuously differentiable on $U$ and satisfies the equation at every point of $U$.
--   2. **Far-field amplitude (eq. 4).** $F:\mathbb{R}\to\mathbb{C}$ is the far-field amplitude of $u$ if there are $C$ and $R_0>0$ with
--   $$\Big|u(r\cos\theta,r\sin\theta)-\frac{e^{ikr}}{\sqrt r}F(\theta)\Big|\le C\,r^{-3/2}\qquad(r\ge R_0,\ \theta\in\mathbb{R}),$$
--   i.e. $u=\frac{e^{ik\rho}}{\sqrt\rho}\big(F(\theta)+O(\rho^{-1})\big)$ uniformly in $\theta$. For a solution of the Helmholtz equation outside a disc, this condition also implies the outgoing radiation condition (it excludes incoming $e^{-ik\rho}$ components); the definition itself does not mention the Helmholtz equation and is always used together with it.
--   3. **Exterior of a circle.** $\{\boldsymbol\rho:|\boldsymbol\rho-\boldsymbol c|>R\}$.
--   4. **Nonradiating field (Section 4.3).** $u$ is nonradiating if its far-field amplitude is $F\equiv0$, so that the radiated power (5) vanishes.
--   5. **TM plane wave (eqs. 7, 8, 10).** $H^{\rm in}(\boldsymbol\rho)=e^{ik(x\cos\alpha+y\sin\alpha)}$, with field vectors $\boldsymbol H^{\rm in}=H^{\rm in}\hat{\boldsymbol z}$ and $\boldsymbol E^{\rm in}=\eta_0H^{\rm in}\,\hat{\boldsymbol z}\times\hat{\boldsymbol k}=\eta_0H^{\rm in}(-\sin\alpha,\cos\alpha,0)$. The case $\alpha=0$ is eq. (10).
--   6. **Time averages (eqs. 5, 6).** With the paper's convention $\boldsymbol H(\boldsymbol\rho,t)=\operatorname{Re}\{\boldsymbol H(\boldsymbol\rho)e^{-i\omega t}\}$, the time-averaged Poynting vector is $\boldsymbol S=\tfrac12\operatorname{Re}(\boldsymbol E\times\overline{\boldsymbol H})$. The incident power density is $|\boldsymbol S^{\rm in}|$. The time-averaged scattered power per unit length through the circle $\rho=r$ is
--   $$P_r(u)=\int_{-\pi}^{\pi}\frac{\eta_0}{2k}\operatorname{Im}\big(\overline{u}\,\partial_\rho u\big)(r,\theta)\,r\,d\theta,$$
--   which is $\int\boldsymbol S^{\rm sc}\cdot\hat{\boldsymbol\rho}\,r\,d\theta$ for $\boldsymbol E^{\rm sc}=\frac{i\eta_0}{k}\nabla\times(u\hat{\boldsymbol z})$ (Maxwell's equations in air). The total scattering cross section (6) is $\Sigma_r=P_r(u)/|\boldsymbol S^{\rm in}|$.
--   7. **Trivial structure (Section 3).** A horizontal wall is a segment $\{(x,c):a\le x\le b\}$ with $a<b$. For two walls, $\Gamma$ is their union and $\Omega=\mathbb{R}^2\setminus\Gamma$. $H^{\rm sc}$ solves the exterior Neumann problem (2)-(4) with incident field $H^{\rm in}$ and far-field amplitude $F$ if three things hold. First, it solves (2) on $\Omega$. Second, at every point $(x,c)$ of a wall with $a<x<b$, the limits of $\partial_yH^{\rm sc}$ from $\Omega$ above and below the wall both equal $-\partial_yH^{\rm in}(x,c)$; this is eq. (3) with $\nu=\hat{\boldsymbol y}$. Third, it satisfies (4) with amplitude $F$.
-- source:
--   Helsing and Karlsson, The uniqueness of inverse scattering problems, reciprocity principles, and nonradiating sources related to low-signature structures, arXiv:2509.26304v1 (2025), Section 2 (eqs. (1)-(9)), Section 3 (eqs. (10)-(12)), Section 4.3

import Mathlib

/-!
Helsing and Karlsson, *The uniqueness of inverse scattering problems, reciprocity principles,
and nonradiating sources related to low-signature structures*, arXiv:2509.26304v1 (2025):
the two-dimensional TM scattering setting of Section 2 (eqs. (1)-(9)), the trivial invisible
structure of Section 3 and the nonradiating fields of Section 4.3.

Points of the cross-section plane `z = 0` are pairs `(x, y) : ℝ × ℝ`; all distances are written
out with the Euclidean formula (the product norm on `ℝ × ℝ` is the sup norm and is not used).
-/

open Filter Topology MeasureTheory

noncomputable section

namespace Arxiv2509_26304

/-- Section 2, eq. (2): the partial derivative `∂u/∂x` of a field `u(x, y)` on the
cross-section plane. -/
def partialX (u : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  deriv (fun x : ℝ => u (x, p.2)) p.1

/-- Section 2, eq. (3): the partial derivative `∂u/∂y` of a field `u(x, y)`; on a horizontal wall
(normal `ν = ±ŷ`) this is, up to sign, the normal derivative `ν · ∇u`. -/
def partialY (u : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  deriv (fun y : ℝ => u (p.1, y)) p.2

/-- Section 2, eq. (2): the two-dimensional Laplacian `∇²u = ∂²u/∂x² + ∂²u/∂y²`. -/
def laplacian2 (u : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  partialX (partialX u) p + partialY (partialY u) p

/-- Section 2, eq. (2): `u` is a classical (twice continuously differentiable) solution of the
Helmholtz equation `(∇² + k²) u = 0` on the set `U`. -/
def IsHelmholtzOn (k : ℝ) (U : Set (ℝ × ℝ)) (u : ℝ × ℝ → ℂ) : Prop :=
  ContDiffOn ℝ 2 u U ∧ ∀ p ∈ U, laplacian2 u p + (k : ℂ) ^ 2 * u p = 0

/-- Section 2, below eq. (4): the point `ρ = ρ (cos θ, sin θ)` with distance `ρ = r` from the
origin and azimuthal angle `θ` measured from the `x`-axis. -/
def polarPoint (r θ : ℝ) : ℝ × ℝ :=
  (r * Real.cos θ, r * Real.sin θ)

/-- Section 2, eq. (4): `F` is the far-field amplitude of `u`, i.e.
`u(ρ) = (e^{ikρ}/√ρ) (F(θ) + O(ρ⁻¹))` as `ρ → ∞`, with the `O`-term uniform in `θ`
(equivalently, the remainder is bounded by `C ρ^{-3/2}` for all large `ρ`). Eq. (4) is also the
outgoing radiation condition of the exterior problem. -/
def HasFarFieldAmplitude (k : ℝ) (u : ℝ × ℝ → ℂ) (F : ℝ → ℂ) : Prop :=
  ∃ C R₀ : ℝ, 0 < R₀ ∧ ∀ r : ℝ, R₀ ≤ r → ∀ θ : ℝ,
    ‖u (polarPoint r θ) -
        Complex.exp (Complex.I * (k : ℂ) * (r : ℂ)) / ((Real.sqrt r : ℝ) : ℂ) * F θ‖ ≤
      C * r ^ (-(3 : ℝ) / 2)

/-- Section 4.3, p. 14: the open exterior `{ρ : |ρ - c| > R}` of the circle of radius `R` centred
at `c`. -/
def exteriorDisc (c : ℝ × ℝ) (R : ℝ) : Set (ℝ × ℝ) :=
  {p | R ^ 2 < (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2}

/-- Section 4.3, p. 14 (definitions of [8, p. 275], [16, p. 1], [14, p. 2]): a radiated field `u`
is nonradiating if it radiates no power, eq. (5), i.e. its far-field amplitude (4) vanishes for
every direction `θ`. -/
def IsNonradiating (k : ℝ) (u : ℝ × ℝ → ℂ) : Prop :=
  HasFarFieldAmplitude k u (fun _ => 0)

/-- Section 2, eqs. (7), (8): the magnetic field `H^in(ρ) = e^{i k·ρ}` (the `ẑ`-component) of the
TM plane wave with wave vector `k (cos α, sin α)`; `α = 0` gives eq. (10), `H^in = e^{ikx}`. -/
def planeWaveH (k α : ℝ) (p : ℝ × ℝ) : ℂ :=
  Complex.exp (Complex.I * (k : ℂ) * ((p.1 * Real.cos α + p.2 * Real.sin α : ℝ) : ℂ))

/-- Section 2, eq. (7): the magnetic field vector `H^in(ρ) ẑ` of the TM plane wave. -/
def planeWaveHVec (k α : ℝ) (p : ℝ × ℝ) : Fin 3 → ℂ :=
  ![0, 0, planeWaveH k α p]

/-- Section 2, eq. (7): the electric field vector `E^in(ρ) = η₀ e^{i k·ρ} ẑ × k̂` of the TM plane
wave, with `ẑ × k̂ = (-sin α, cos α, 0)` for `k̂ = (cos α, sin α, 0)` (eq. (8)). -/
def planeWaveEVec (eta0 k α : ℝ) (p : ℝ × ℝ) : Fin 3 → ℂ :=
  ![-((eta0 * Real.sin α : ℝ) : ℂ) * planeWaveH k α p,
    ((eta0 * Real.cos α : ℝ) : ℂ) * planeWaveH k α p, 0]

/-- Section 2, p. 4: the time average `½ Re(E × H̄)` of the Poynting vector of the time-harmonic
fields `Re{E e^{-iωt}}`, `Re{H e^{-iωt}}` (the paper's time convention). -/
def timeAvgPoynting (E H : Fin 3 → ℂ) : Fin 3 → ℝ :=
  fun i => (1 / 2 : ℝ) * (crossProduct E (fun j => (starRingEnd ℂ) (H j)) i).re

/-- Section 2, eq. (6), denominator: the time average of the incident power density of the plane
wave (7), the Euclidean length of its time-averaged Poynting vector at the point `p`. -/
def incidentPowerDensity (eta0 k α : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.sqrt (∑ i, (timeAvgPoynting (planeWaveEVec eta0 k α p) (planeWaveHVec k α p) i) ^ 2)

/-- Section 2, eqs. (5), (6), numerator: the time average of the power per unit length radiated by
the scattered field `H^sc = u` through the circle `|ρ| = r`, i.e. `∫_{-π}^{π} S · ρ̂ r dθ` with
`S = ½ Re(E^sc × H̄^sc)` and `E^sc = (i η₀ / k) ∇ × (H^sc ẑ)` (Maxwell's equations in air,
`ω ε₀ = k / η₀`), which gives `S · ρ̂ = (η₀ / (2k)) Im(H̄^sc ∂_ρ H^sc)`. -/
def scatteredPower (eta0 k : ℝ) (u : ℝ × ℝ → ℂ) (r : ℝ) : ℝ :=
  ∫ θ in (-Real.pi)..Real.pi,
    eta0 / (2 * k) *
      ((starRingEnd ℂ) (u (polarPoint r θ)) * deriv (fun s : ℝ => u (polarPoint s θ)) r).im * r

/-- Section 2, eq. (6): the total scattering cross section of the scattered field `u` of the plane
wave (7) with angle of incidence `α`, measured through the circle `|ρ| = r`: time-averaged
scattered power per unit length divided by the time-averaged incident power density (which does
not depend on the point; it is evaluated at the origin). -/
def scatteringCrossSection (eta0 k α : ℝ) (u : ℝ × ℝ → ℂ) (r : ℝ) : ℝ :=
  scatteredPower eta0 k u r / incidentPowerDensity eta0 k α (0, 0)

/-- Section 3, eqs. (11), (12): an infinitely thin, flat horizontal PEC wall
`{(x, c) : a ≤ x ≤ b}` parallel to the `x`-axis. -/
structure HorizontalWall where
  /-- left end of the wall -/
  a : ℝ
  /-- right end of the wall -/
  b : ℝ
  /-- height of the wall -/
  c : ℝ
  hab : a < b

/-- Section 3: the point set `{(x, c) : a ≤ x ≤ b}` of a horizontal wall. -/
def HorizontalWall.carrier (w : HorizontalWall) : Set (ℝ × ℝ) :=
  {p | w.a ≤ p.1 ∧ p.1 ≤ w.b ∧ p.2 = w.c}

/-- Section 2 and Section 3, p. 5: the boundary `Γ` of a structure consisting only of the two
horizontal walls `w₁`, `w₂` (the trivial structure). -/
def wallsGamma (w₁ w₂ : HorizontalWall) : Set (ℝ × ℝ) :=
  w₁.carrier ∪ w₂.carrier

/-- Section 2: the domain `Ω` exterior to `Γ` (the complement of the two walls), filled with air. -/
def wallsOmega (w₁ w₂ : HorizontalWall) : Set (ℝ × ℝ) :=
  (wallsGamma w₁ w₂)ᶜ

/-- Section 2, eq. (3) on a horizontal wall `w` (normal `ν = ŷ`): at every point `(x, c)` of the
wall with `a < x < b`, the normal derivative `ν · ∇H^sc = ∂H^sc/∂y`, taken as a limit from `Ω`
on each side of the wall (above and below), equals `-ν · ∇H^in = -∂H^in/∂y`. -/
def SatisfiesNeumannOnWall (Ω : Set (ℝ × ℝ)) (w : HorizontalWall) (Hin Hsc : ℝ × ℝ → ℂ) :
    Prop :=
  ∀ x : ℝ, w.a < x → x < w.b →
    Tendsto (partialY Hsc) (𝓝[Ω ∩ {q | w.c < q.2}] (x, w.c)) (𝓝 (-partialY Hin (x, w.c))) ∧
    Tendsto (partialY Hsc) (𝓝[Ω ∩ {q | q.2 < w.c}] (x, w.c)) (𝓝 (-partialY Hin (x, w.c)))

/-- Section 2, eqs. (2)-(4), for the structure consisting only of the two horizontal walls
`w₁`, `w₂`: `Hsc` solves the exterior Neumann problem with incident field `Hin`, i.e. the
Helmholtz equation (2) in `Ω`, the boundary condition (3) on both walls, and the asymptotics (4)
with far-field amplitude `F`. -/
def IsWallsNeumannSolution (k : ℝ) (w₁ w₂ : HorizontalWall) (Hin Hsc : ℝ × ℝ → ℂ)
    (F : ℝ → ℂ) : Prop :=
  IsHelmholtzOn k (wallsOmega w₁ w₂) Hsc ∧
    SatisfiesNeumannOnWall (wallsOmega w₁ w₂) w₁ Hin Hsc ∧
    SatisfiesNeumannOnWall (wallsOmega w₁ w₂) w₂ Hin Hsc ∧
    HasFarFieldAmplitude k Hsc F

end Arxiv2509_26304


