-- Prove2me | Definitions.Def_Arxiv1611_09952_Basic
-- name    : Arxiv1611_09952_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T23:45:13.57196+00:00
-- url     : https://prove2.me/theorems/89ac4cf4-e8a9-4950-b13b-3125e9efcaae
-- title:
--   Obstacles, scattering solutions, scattering amplitude and Dirichlet Green's function in $\mathbb{R}^3$
-- statement:
--   Objects of Sections 1 and 2 of Ramm, *Inverse obstacle scattering with non-over-determined data* (arXiv:1611.09952v2).
--
--   1. **Obstacle.** An obstacle is a bounded domain (open, connected) $D\subset\mathbb{R}^3$ whose boundary $S=\partial D$ is connected and $C^2$: near every $p\in S$, after an orthogonal change of coordinates, $D$ is the region $\{x_3<\varphi(x_1,x_2)\}$ below the graph of a $C^2$ function. The exterior is $D'=\mathbb{R}^3\setminus D$; its interior is $\mathbb{R}^3\setminus\overline D$.
--   2. **Normal and normal derivative.** $N(s)$ is the unit normal at $s\in S$ pointing out of $D$, characterised by the requirement that the tangent cone of $D$ at $s$ is the half-space $\{v:\langle v,N(s)\rangle\le0\}$. The normal derivative is $u_N(s)=\lim_{x\to s,\ x\notin\overline D}\nabla u(x)\cdot N(s)$.
--   3. **Scattering problem (eqs. (1)-(3)).** For $k>0$ and $\alpha\in S^2$, the scattering solution $u$ is a $C^2$ solution of $(\nabla^2+k^2)u=0$ in $\mathbb{R}^3\setminus\overline D$ which, together with its gradient, extends continuously to $D'$, satisfies $\Gamma u=0$ on $S$, and is such that $v=u-e^{ik\alpha\cdot x}$ satisfies the radiation condition $|x|\,(v_r-ikv)\to0$ as $|x|\to\infty$, uniformly in $x/|x|$. The boundary operator is $\Gamma_1u=u$ (Dirichlet), $\Gamma_2u=u_N$ (Neumann) or $\Gamma_3u=u_N+hu$ (impedance) with a constant $h$, $\operatorname{Im}h\ge0$, $h\neq0$.
--   4. **Scattering amplitude (eq. (4)).** $A(\beta)=A(\beta,\alpha,k)$ is defined by $v(r\beta)=A(\beta)\,e^{ikr}/r+o(1/r)$ as $r\to\infty$, i.e. $r e^{-ikr}v(r\beta)\to A(\beta)$ for every $\beta\in S^2$.
--   5. **Green's functions (Section 2).** $g(r)=e^{ikr}/(4\pi r)$ and $g(x,y)=g(|x-y|)$. The Dirichlet Green's function $G(x,y)$ of the Helmholtz operator in $D'$ is, for each $y$ outside $\overline D$, of the form $g(x,y)+w_y(x)$ with $w_y$ a Helmholtz solution outside $\overline D$; $G(\cdot,y)$ is continuous on $D'\setminus\{y\}$, radiating, and $G(x,y)=0$ when $x\ne y$ lie in $D'$ and one of them lies on $S$.
--   6. **Surface measure.** $ds$ on a surface $\Sigma\subset\mathbb{R}^3$ is two-dimensional Hausdorff measure on $\Sigma$ normalised to area.
--
--   **Formalization Note** Mathlib's two-dimensional Hausdorff measure $\mu_H^2$ is not normalised (it sums $\operatorname{diam}^2$), so the area measure is $\tfrac{\pi}{4}\mu_H^2$. The impedance condition is required to have $h\neq0$ because $h=0$ is the Neumann condition, which the paper lists separately; this way, equality of boundary conditions means the same condition. The scattering solution is required to be $C^1$ up to $S$, which the actual solution is for a $C^2$ boundary; this is what makes $u|_S$ and $u_N$ meaningful.
-- source:
--   A. G. Ramm, Inverse obstacle scattering with non-over-determined data, arXiv:1611.09952v2 (2017), https://arxiv.org/abs/1611.09952, Section 1, eqs. (1)-(4), PDF pp. 1-2; Section 2, Lemma 1 and the Green's functions G, G_m, PDF p. 4; surface integrals of Lemmas 2 and 5, PDF pp. 5, 7

import Mathlib

/-!
A. G. Ramm, *Inverse obstacle scattering with non-over-determined data*, arXiv:1611.09952v2
(2017): obstacles with connected `C²` boundary in `ℝ³`, the scattering problem (1)-(2) with the
boundary conditions (3), the scattering amplitude (4), the Dirichlet Green's function of
Section 2, and the surface measure used in Lemmas 2 and 5.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace Arxiv1611_09952

/-- Section 1: the physical space `ℝ³`. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- Section 1: the boundary of `D` is `C²`-smooth. Near every boundary point `p`, after a rigid
rotation `R` of coordinates, `D` is the region below the graph of a `C²` function `φ` of the
first two coordinates. -/
def HasC2Boundary (D : Set E3) : Prop :=
  ∀ p ∈ frontier D, ∃ (R : E3 ≃ₗᵢ[ℝ] E3) (φ : ℝ × ℝ → ℝ) (r : ℝ), 0 < r ∧ ContDiff ℝ 2 φ ∧
    ∀ x ∈ Metric.ball p r, (x ∈ D ↔ (R x) 2 < φ ((R x) 0, (R x) 1))

/-- Section 1: an obstacle is a bounded domain (open, connected) `D ⊂ ℝ³` whose boundary
`S = ∂D` is connected and `C²`-smooth. -/
def IsObstacle (D : Set E3) : Prop :=
  IsOpen D ∧ IsConnected D ∧ Bornology.IsBounded D ∧ IsConnected (frontier D) ∧ HasC2Boundary D

/-- Section 1: the open exterior `ℝ³ \ closure D`, where the Helmholtz equation (1) holds. The
paper's `D' := ℝ³ \ D` is its closure `Dᶜ`, which contains `S`. -/
def openExterior (D : Set E3) : Set E3 := (closure D)ᶜ

/-- Section 1, eq. (3): `n` is the unit normal to `∂D` at `s` pointing out of `D`, characterised
geometrically: the tangent cone of `D` at `s` is the half-space `{v : ⟨v, n⟩ ≤ 0}`. -/
def IsOuterNormal (D : Set E3) (s n : E3) : Prop :=
  s ∈ frontier D ∧ ‖n‖ = 1 ∧ tangentConeAt ℝ D s = {v | inner ℝ v n ≤ 0}

open Classical in
/-- The outward unit normal `N(s)` of `D` at `s` (eq. (3)); `0` where `∂D` has no normal. -/
def outerNormal (D : Set E3) (s : E3) : E3 :=
  if h : ∃ n, IsOuterNormal D s n then h.choose else 0

/-- One-sided derivative of `u` at a point `s` in direction `n`, computed as the limit of the
derivative `∇u(x) · n` as `x → s` inside the open set `U` where `u` is differentiable. -/
def boundaryDeriv (U : Set E3) (n : E3) (u : E3 → ℂ) (s : E3) : ℂ :=
  limUnder (𝓝[U] s) (fun x => fderiv ℝ u x n)

/-- Eq. (3): the normal derivative `u_N(s)` on `S = ∂D` of a function `u` defined outside `D`,
with `N` pointing out of `D`. -/
def normalDeriv (D : Set E3) (u : E3 → ℂ) (s : E3) : ℂ :=
  boundaryDeriv (openExterior D) (outerNormal D s) u s

/-- Eq. (1): `u` is a classical solution of the Helmholtz equation `(∇² + k²)u = 0` on `U`. -/
def IsHelmholtzOn (k : ℝ) (U : Set E3) (u : E3 → ℂ) : Prop :=
  ContDiffOn ℝ 2 u U ∧ ∀ x ∈ U, Laplacian.laplacian u x + ((k : ℂ) ^ 2) * u x = 0

/-- `u` is `C¹` up to the boundary of the exterior: `u` and its derivative extend continuously
from the open exterior to `D' = ℝ³ \ D`, so that `u|_S` and `u_N` exist. -/
def IsC1UpToBoundary (D : Set E3) (u : E3 → ℂ) : Prop :=
  ContinuousOn u Dᶜ ∧ ∃ Du : E3 → (E3 →L[ℝ] ℂ), ContinuousOn Du Dᶜ ∧
    ∀ x ∈ openExterior D, fderiv ℝ u x = Du x

/-- Eq. (1): the incident plane wave `e^{ik α·x}`. -/
def planeWave (k : ℝ) (α x : E3) : ℂ := Complex.exp (Complex.I * k * (inner ℝ α x : ℝ))

/-- Eq. (2): the Sommerfeld radiation condition `v_r - ikv = o(1/r)`, `r = |x| → ∞`, uniformly
in the direction `x/r`. -/
def SatisfiesRadiation (k : ℝ) (v : E3 → ℂ) : Prop :=
  Tendsto (fun x : E3 => (‖x‖ : ℂ) * (fderiv ℝ v x (‖x‖⁻¹ • x) - Complex.I * k * v x))
    (cocompact E3) (𝓝 0)

/-- Eq. (3): the three boundary conditions `Γ₁u = u`, `Γ₂u = u_N`, `Γ₃u = u_N + hu`
(Dirichlet, Neumann, impedance with constant impedance `h`). -/
inductive BoundaryCondition
  | dirichlet
  | neumann
  | impedance (h : ℂ)
  deriving DecidableEq

/-- Eq. (3): the admissible boundary conditions. For the impedance condition `h` is a constant
with `Im h ≥ 0`; `h ≠ 0` because `h = 0` is the Neumann condition `Γ₂`, which the paper lists
separately (see the end of the proof of Theorem 1). -/
def BoundaryCondition.Admissible : BoundaryCondition → Prop
  | .dirichlet => True
  | .neumann => True
  | .impedance h => 0 ≤ h.im ∧ h ≠ 0

/-- Eq. (1): `Γ_j u = 0` on `S = ∂D`. -/
def SatisfiesBC (D : Set E3) : BoundaryCondition → (E3 → ℂ) → Prop
  | .dirichlet, u => ∀ s ∈ frontier D, u s = 0
  | .neumann, u => ∀ s ∈ frontier D, normalDeriv D u s = 0
  | .impedance h, u => ∀ s ∈ frontier D, normalDeriv D u s + h * u s = 0

/-- Eqs. (1)-(2): `u` is the scattering solution for the obstacle `D` with boundary condition
`bc`, wave number `k` and incident direction `α`: it solves the Helmholtz equation in the
exterior, is `C¹` up to `S`, satisfies `Γ u = 0` on `S`, and `v = u - e^{ikα·x}` satisfies the
radiation condition. -/
def IsScatteringSolution (D : Set E3) (bc : BoundaryCondition) (k : ℝ) (α : E3)
    (u : E3 → ℂ) : Prop :=
  IsHelmholtzOn k (openExterior D) u ∧ IsC1UpToBoundary D u ∧ SatisfiesBC D bc u ∧
    SatisfiesRadiation k (fun x => u x - planeWave k α x)

/-- Eq. (4): `A(β) = A(β, α, k)` is the scattering amplitude of `u`:
`v = A(β) e^{ikr}/r + o(1/r)` as `r = |x| → ∞`, `x/r = β`, i.e. `r e^{-ikr} v(rβ) → A(β)` for
every `β ∈ S²`. -/
def HasScatteringAmplitude (k : ℝ) (α : E3) (u : E3 → ℂ) (A : E3 → ℂ) : Prop :=
  ∀ β ∈ Metric.sphere (0 : E3) 1,
    Tendsto (fun r : ℝ => (r : ℂ) * Complex.exp (-(Complex.I * k * r)) *
      (u (r • β) - planeWave k α (r • β))) atTop (𝓝 (A β))

/-- Section 2, after Lemma 1: `g(r) = e^{ikr}/(4πr)`. -/
def gRad (k r : ℝ) : ℂ := Complex.exp (Complex.I * k * r) / (4 * Real.pi * r)

/-- Section 2, proof of Lemma 4: the free outgoing Green's function
`g(x, y) = e^{ik|x-y|}/(4π|x-y|)`. -/
def freeGreen (k : ℝ) (x y : E3) : ℂ := gRad k ‖x - y‖

/-- Section 2: `G` is the Green's function of the Dirichlet Helmholtz operator in `D'`
(`(∇² + k²)G = -δ(x - y)`, `G = 0` on `S`, radiating). For each `y` in the open exterior,
`G(·, y) - g(·, y)` is a Helmholtz solution in the open exterior, `G(·, y)` is continuous on
`D' \ {y}` and satisfies the radiation condition, and `G(x, y) = 0` whenever `x ≠ y` lie in `D'`
and one of them lies on `S`. -/
def IsDirichletGreen (D : Set E3) (k : ℝ) (G : E3 → E3 → ℂ) : Prop :=
  (∀ y ∈ openExterior D,
    (∃ w : E3 → ℂ, IsHelmholtzOn k (openExterior D) w ∧
      ∀ x ∈ openExterior D, x ≠ y → G x y = freeGreen k x y + w x) ∧
    ContinuousOn (fun x => G x y) (Dᶜ \ {y}) ∧
    SatisfiesRadiation k (fun x => G x y)) ∧
  ∀ x ∈ Dᶜ, ∀ y ∈ Dᶜ, x ≠ y → (x ∈ frontier D ∨ y ∈ frontier D) → G x y = 0

/-- The surface area measure on a surface `S ⊂ ℝ³`: two-dimensional Hausdorff measure restricted
to `S`, scaled by `π/4` (Mathlib's `μH[2]` is not normalised; `π/4 · μH[2]` is area). -/
def surfaceMeasure (S : Set E3) : Measure E3 :=
  ENNReal.ofReal (Real.pi / 4) • (μH[2]).restrict S

end Arxiv1611_09952


