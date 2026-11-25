-- Prove2me | Definitions.Def_Arxiv2602_11197_Basic
-- name    : Arxiv2602_11197_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T20:16:41.506448+00:00
-- url     : https://prove2.me/theorems/15bd023e-4227-437e-9297-cd7fd833728b
-- title:
--   Helmholtz boundary-value problem and residual scattering problem on a rectangle
-- statement:
--   Objects of Section 3 and Section 3.2 of Balaji, Teolis, Mis, Lara Benitez, Wang and de Hoop (2026).
--
--   1. **Domain.** For side lengths $L_1,L_2>0$, $\Omega=(0,L_1)\times(0,L_2)\subset\mathbb{R}^2$, with $x_1$ horizontal and $x_2$ the depth. The free surface $\Gamma_{\mathrm{Free}}$ is the top edge $\{x_2=0\}$, end points included. The absorbing boundary $\Gamma_{\mathrm{ABC}}$ consists of the left, right and bottom edges without their end points. On these edges the outward unit normal $\nu$ is $(-1,0)$, $(1,0)$ and $(0,1)$ respectively.
--   2. **Normal derivative.** $\partial_\nu u(x)$ is the derivative of $u$ within the closed rectangle $\overline\Omega$ at $x$, in the direction $\nu(x)$.
--   3. **Helmholtz problem, eq. (1).** For an angular frequency $\omega$, a wavespeed $c$ and a source $s$, a complex field $p$ solves eq. (1) if three conditions hold:
--      - in $\Omega$, $\big[\Delta+\omega^2/c(x)^2\big]p(x)=-s(x)$ at almost every $x$, where $p$ is twice continuously differentiable near each such $x$;
--      - $\partial_\nu p-\frac{i\omega}{c}p=0$ on $\Gamma_{\mathrm{ABC}}$, where $p$ is differentiable within $\overline\Omega$;
--      - $p=0$ on $\Gamma_{\mathrm{Free}}$.
--   4. **Contrast.** $\delta m(x)=v(x)^{-2}-v_{\mathrm{bg}}(x)^{-2}$.
--   5. **Residual problem, eq. (2), as printed.** $\delta p$ solves eq. (2) for $(v,v_{\mathrm{bg}},p_{\mathrm{bg}})$ if three conditions hold:
--      - $\big[\Delta+\omega^2/v_{\mathrm{bg}}^2\big]\delta p=-\omega^2\,\delta m\,(\delta p+p_{\mathrm{bg}})$ in $\Omega$, in the same almost-everywhere sense as above;
--      - $\partial_\nu\delta p-\frac{i\omega}{v}\delta p=0$ on $\Gamma_{\mathrm{ABC}}$;
--      - $\delta p=0$ on $\Gamma_{\mathrm{Free}}$.
--   6. **Residual problem with the derived absorbing condition.** This is the same as item 5, except that on $\Gamma_{\mathrm{ABC}}$ the condition is
--   $$\partial_\nu\delta p-\frac{i\omega}{v}\delta p=i\omega\Big(\frac1v-\frac1{v_{\mathrm{bg}}}\Big)p_{\mathrm{bg}}.$$
--   This is the condition that subtracting eq. (1) for $v_{\mathrm{bg}}$ from eq. (1) for $v$ produces.
--
--   **Formalization Note** The printed absorbing line of eq. (1) reads "$\partial_\nu p-\frac{i\omega}{v}$" with neither $p$ nor "$=0$". It is read as $\partial_\nu p-\frac{i\omega}{v}p=0$, the form used in eq. (2).
--
--   The paper does not say in what sense eq. (1) holds. For the paper's piecewise-constant wavespeeds, $p$ cannot be twice differentiable across a salt interface. For this reason the interior equation is required at almost every point of $\Omega$, with $p$ of class $C^2$ near each such point, rather than at every point.
--
--   Functions are defined on all of $\mathbb{R}^2$. Only their values on $\overline\Omega$ enter the boundary conditions, and only their values near points of $\Omega$ enter the interior equation.
--
--   The paper does not say which end points of the edges belong to $\Gamma_{\mathrm{ABC}}$ or $\Gamma_{\mathrm{Free}}$. The corners are assigned as stated in item 1.
-- source:
--   Balaji, Teolis, Mis, Lara Benitez, Wang and de Hoop, Hybrid operator learning of wave scattering maps in high-contrast media, arXiv:2602.11197v1 (2026), Section 3 eq. (1) (PDF p. 3) and Section 3.2 eq. (2) (PDF p. 4)

import Mathlib

/-!
Balaji, Teolis, Mis, Lara Benitez, Wang and de Hoop, *Hybrid operator learning of wave scattering
maps in high-contrast media*, arXiv:2602.11197v1 (2026): the rectangular domain and its boundary parts,
the Helmholtz boundary-value problem, eq. (1) of Section 3, and the residual (scattering) problem,
eq. (2) of Section 3.2.
-/

open MeasureTheory

noncomputable section

namespace Arxiv2602_11197

/-- The plane `ℝ²` with its Euclidean structure (Section 3: `Ω ⊂ ℝ²`). -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Section 3: the rectangular domain `Ω = (0, L₁) × (0, L₂)`. Coordinate `0` is horizontal and
coordinate `1` is depth, so the edge `x 1 = 0` is the top of the domain. -/
def domain (L₁ L₂ : ℝ) : Set Plane :=
  {x | 0 < x 0 ∧ x 0 < L₁ ∧ 0 < x 1 ∧ x 1 < L₂}

/-- Section 3: the closed rectangle `[0, L₁] × [0, L₂]`, the closure of `Ω`. -/
def closedDomain (L₁ L₂ : ℝ) : Set Plane :=
  {x | 0 ≤ x 0 ∧ x 0 ≤ L₁ ∧ 0 ≤ x 1 ∧ x 1 ≤ L₂}

/-- Section 3: the free-surface edge `Γ_Free`, the top edge `{x 1 = 0}` of the rectangle
(the point source of Appendix C sits at its centre), including its two end points. -/
def freeBoundary (L₁ : ℝ) : Set Plane :=
  {x | 0 ≤ x 0 ∧ x 0 ≤ L₁ ∧ x 1 = 0}

/-- Section 3: the absorbing boundary `Γ_ABC`, consisting of the other three edges of the rectangle
(left, right and bottom), each without its end points, where the outward normal is defined. -/
def absorbingBoundary (L₁ L₂ : ℝ) : Set Plane :=
  {x | x 0 = 0 ∧ 0 < x 1 ∧ x 1 < L₂} ∪ {x | x 0 = L₁ ∧ 0 < x 1 ∧ x 1 < L₂} ∪
    {x | 0 < x 0 ∧ x 0 < L₁ ∧ x 1 = L₂}

open Classical in
/-- Section 3: the outward unit normal `ν` on `Γ_ABC`: `(-1, 0)` on the left edge, `(1, 0)` on the
right edge and `(0, 1)` on the bottom edge. -/
def outwardNormal (L₁ : ℝ) (x : Plane) : Plane :=
  if x 0 = 0 then EuclideanSpace.single 0 (-1)
  else if x 0 = L₁ then EuclideanSpace.single 0 1
  else EuclideanSpace.single 1 1

/-- Section 3, eq. (1): the normal derivative `∂_ν u(x)` on `Γ_ABC`, the derivative of `u` within
the closed rectangle in the direction of the outward normal. -/
def normalDeriv (L₁ L₂ : ℝ) (u : Plane → ℂ) (x : Plane) : ℂ :=
  fderivWithin ℝ u (closedDomain L₁ L₂) x (outwardNormal L₁ x)

/-- Section 3, eq. (1): the Helmholtz operator `[Δ + ω² / c(x)²] u(x)` for a wavespeed `c`. -/
def helmholtzOp (ω : ℝ) (c : Plane → ℝ) (u : Plane → ℂ) (x : Plane) : ℂ :=
  Laplacian.laplacian u x + ((ω ^ 2 / c x ^ 2 : ℝ) : ℂ) * u x

/-- Section 3, eq. (1): `p` solves the Helmholtz problem with wavespeed `c`, source `s` and angular
frequency `ω`: `[Δ + ω²/c²] p = -s` in `Ω` (at almost every point of `Ω`, at which `p` is twice
continuously differentiable), `∂_ν p - (iω/c) p = 0` on `Γ_ABC`, and `p = 0` on `Γ_Free`.
The absorbing condition is read with `p` and `= 0`, as in eq. (2); the printed line of eq. (1)
omits both. -/
def IsHelmholtzSolution (L₁ L₂ ω : ℝ) (c : Plane → ℝ) (s p : Plane → ℂ) : Prop :=
  (∀ᵐ x ∂(volume.restrict (domain L₁ L₂)),
      ContDiffAt ℝ 2 p x ∧ helmholtzOp ω c p x = -s x) ∧
    (∀ x ∈ absorbingBoundary L₁ L₂, DifferentiableWithinAt ℝ p (closedDomain L₁ L₂) x ∧
      normalDeriv L₁ L₂ p x - Complex.I * (ω : ℂ) / (c x : ℂ) * p x = 0) ∧
    (∀ x ∈ freeBoundary L₁, p x = 0)

/-- Section 3.2: the squared-slowness contrast `δm(x) = v(x)⁻² - v_bg(x)⁻²`. -/
def deltaM (v vbg : Plane → ℝ) (x : Plane) : ℝ :=
  (v x ^ 2)⁻¹ - (vbg x ^ 2)⁻¹

/-- Section 3.2, eq. (2), as printed: `δp` solves the residual problem
`[Δ + ω²/v_bg²] δp = -ω² δm (δp + p_bg)` in `Ω` (at almost every point of `Ω`, at which `δp` is
twice continuously differentiable), `∂_ν δp - (iω/v) δp = 0` on `Γ_ABC`, and `δp = 0` on
`Γ_Free`. -/
def IsResidualSolution (L₁ L₂ ω : ℝ) (v vbg : Plane → ℝ) (pbg dp : Plane → ℂ) : Prop :=
  (∀ᵐ x ∂(volume.restrict (domain L₁ L₂)),
      ContDiffAt ℝ 2 dp x ∧
        helmholtzOp ω vbg dp x = -((ω ^ 2 * deltaM v vbg x : ℝ) : ℂ) * (dp x + pbg x)) ∧
    (∀ x ∈ absorbingBoundary L₁ L₂, DifferentiableWithinAt ℝ dp (closedDomain L₁ L₂) x ∧
      normalDeriv L₁ L₂ dp x - Complex.I * (ω : ℂ) / (v x : ℂ) * dp x = 0) ∧
    (∀ x ∈ freeBoundary L₁, dp x = 0)

/-- Section 3.2, eq. (2), with the absorbing condition that subtracting eq. (1) for `v_bg` from
eq. (1) for `v` produces: the interior equation and the free-surface condition of eq. (2), and
`∂_ν δp - (iω/v) δp = iω (1/v - 1/v_bg) p_bg` on `Γ_ABC` in place of the printed `= 0`. -/
def IsResidualSolutionDerived (L₁ L₂ ω : ℝ) (v vbg : Plane → ℝ) (pbg dp : Plane → ℂ) : Prop :=
  (∀ᵐ x ∂(volume.restrict (domain L₁ L₂)),
      ContDiffAt ℝ 2 dp x ∧
        helmholtzOp ω vbg dp x = -((ω ^ 2 * deltaM v vbg x : ℝ) : ℂ) * (dp x + pbg x)) ∧
    (∀ x ∈ absorbingBoundary L₁ L₂, DifferentiableWithinAt ℝ dp (closedDomain L₁ L₂) x ∧
      normalDeriv L₁ L₂ dp x - Complex.I * (ω : ℂ) / (v x : ℂ) * dp x =
        Complex.I * (ω : ℂ) * (((v x)⁻¹ - (vbg x)⁻¹ : ℝ) : ℂ) * pbg x) ∧
    (∀ x ∈ freeBoundary L₁, dp x = 0)

end Arxiv2602_11197


