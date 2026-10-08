-- Prove2me | Definitions.Def_HryniewiczCriterion_GlobalSection
-- name    : HryniewiczCriterion_GlobalSection
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-10-05T18:11:47.250992+00:00
-- url     : https://prove2.me/theorems/5e107c9d-edd3-499b-90e9-e4c18855454d
-- title:
--   Disk-like global surfaces of section, unknots, adapted open books
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ carry the flow of $X_H$, and let $P=(x,T)$ be a periodic orbit. Write $\mathbb{D}$ for the closed unit disk in $\mathbb{R}^2$ and $\partial\mathbb{D}$ for the unit circle.
--
--   1. A **smooth disk embedding** is a smooth map $e:\mathbb{R}^2\to\mathbb{R}^4$ that is injective on $\mathbb{D}$ and has injective differential at every point of $\mathbb{D}$, boundary included.
--   2. $P$ **bounds a disk-like global surface of section** if there is a smooth disk embedding $e$ with $D=e(\mathbb{D})\subset S$ such that
--      1. $e(\partial\mathbb{D})=x(\mathbb{R})$;
--      2. $X_H$ is transverse to $D\setminus\partial D$, i.e. $X_H(e(u))\notin \operatorname{im} de(u)$ for $|u|<1$;
--      3. every trajectory $y$ on $S$ with $y(0)\notin x(\mathbb{R})$ meets $D$ at arbitrarily large positive and arbitrarily large negative times.
--   3. $P$ is **unknotted** if $x(\mathbb{R})=e(\partial\mathbb{D})$ for some smooth disk embedding $e$ with $e(\mathbb{D})\subset S$.
--   4. An **adapted open book decomposition with disk-like pages and binding $P$** is a smooth family $\theta\mapsto e_\theta$, $\theta\in\mathbb{R}/\mathbb{Z}$, such that:
--      1. every $e_\theta$ parametrizes a disk-like global surface of section bounded by $P$;
--      2. $e_\theta(\cos2\pi t,\sin2\pi t)=x(Tt)$ for all $\theta,t$, so the binding carries the orientation of the flow;
--      3. every page is positively oriented by $d\lambda_0=\omega_0$;
--      4. $(\theta,u)\mapsto e_\theta(u)$ maps $\mathbb{R}/\mathbb{Z}\times\operatorname{int}\mathbb{D}$ bijectively onto $S\setminus x(\mathbb{R})$ with injective differential.
--      Then $\theta$ is a smooth fibration $S\setminus x(\mathbb{R})\to\mathbb{R}/\mathbb{Z}$ whose fibres are the interiors of the pages, as in Definition 1.2.
--
--   These are the notions in which Hryniewicz's criterion (Theorem 1.7) and Theorem 1.8 are stated.
--
--   **Formalization Note** Smoothness up to the boundary of $\mathbb{D}$ is encoded by asking for a smooth map on all of $\mathbb{R}^2$. The open book stores a page map `ℝ → ℝ² → ℝ⁴`, $1$-periodic in $\theta$, together with its properties.
-- source:
--   Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014) 791-862, https://arxiv.org/abs/1105.2077, p. 1 (global surface of section), p. 2 (open book decomposition, Definition 1.2), p. 3 (unknotted)

import Definitions.Def_HryniewiczCriterion_Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Disk-like global surfaces of section, unknots and adapted open books

Hryniewicz, arXiv:1105.2077, §1 (pp. 1–2): global surfaces of section, open book
decompositions and Definition 1.2 (adapted open books), specialized to disk-like
surfaces on a star-shaped level `S = H⁻¹(1)` with the flow of `X_H`.
-/

namespace HryniewiczCriterion

noncomputable section

open scoped ContDiff

/-- Parameter plane `ℝ²` of a disk. -/
abbrev Plane := Fin 2 → ℝ

def closedUnitDisk : Set Plane := {u | u 0 ^ 2 + u 1 ^ 2 ≤ 1}

def openUnitDisk : Set Plane := {u | u 0 ^ 2 + u 1 ^ 2 < 1}

def unitCircle : Set Plane := {u | u 0 ^ 2 + u 1 ^ 2 = 1}

/-- The point `(cos 2πt, sin 2πt)`; it runs once counterclockwise around the unit
circle as `t` runs over `[0, 1]`. -/
def circlePoint (t : ℝ) : Plane := ![Real.cos (2 * Real.pi * t), Real.sin (2 * Real.pi * t)]

/-- `e` restricts to a smooth embedding of the closed unit disk: `e` is smooth,
injective on the disk, with injective differential at every point of the disk
(boundary included). -/
def IsSmoothDiskEmbedding (e : Plane → R4) : Prop :=
  ContDiff ℝ ∞ e ∧ Set.InjOn e closedUnitDisk ∧
    ∀ u ∈ closedUnitDisk, Function.Injective (fderiv ℝ e u)

/-- `e` parametrizes a disk-like global surface of section `D = e(closed disk) ⊆ S`
bounded by `P`: `∂D = e(circle)` is the image of `P`; `X_H` is transverse to
`D \ ∂D`; and every trajectory on `S` not contained in `∂D` meets `D` at arbitrarily
large positive and at arbitrarily large negative times. -/
def IsDiskLikeGlobalSectionMap (H : R4 → ℝ) (P : PeriodicOrbit H) (e : Plane → R4) :
    Prop :=
  IsSmoothDiskEmbedding e ∧
  e '' closedUnitDisk ⊆ energySurface H ∧
  e '' unitCircle = P.image ∧
  (∀ u ∈ openUnitDisk,
    hamiltonianVectorField H (e u) ∉ Set.range (fderiv ℝ e u)) ∧
  ∀ y : ℝ → R4, IsTrajectory H y → y 0 ∉ P.image → ∀ a : ℝ,
    (∃ t, a < t ∧ y t ∈ e '' closedUnitDisk) ∧ (∃ t, t < a ∧ y t ∈ e '' closedUnitDisk)

/-- `P` bounds a disk-like global surface of section. -/
def BoundsDiskLikeGlobalSection (H : R4 → ℝ) (P : PeriodicOrbit H) : Prop :=
  ∃ e : Plane → R4, IsDiskLikeGlobalSectionMap H P e

/-- `P` is unknotted: its image is the boundary of a smoothly embedded closed disk
in `S`. -/
def IsUnknotted (H : R4 → ℝ) (P : PeriodicOrbit H) : Prop :=
  ∃ e : Plane → R4, IsSmoothDiskEmbedding e ∧ e '' closedUnitDisk ⊆ energySurface H ∧
    e '' unitCircle = P.image

/-- An open book decomposition of `S` with disk-like pages and binding `P`, adapted
to the flow (Definition 1.2). Pages are `page θ (closed disk)`, `θ ∈ ℝ/ℤ`:
1. the page family is smooth in `(θ, u)` and `1`-periodic in `θ`;
2. every page is a disk-like global surface of section bounded by `P`;
3. every boundary circle runs along `P` in the flow direction:
   `page θ (cos 2πt, sin 2πt) = x(Tt)` (binding orientation = orientation of `P`);
4. pages are positively oriented by `dλ₀ = ω₀`;
5. `(θ, u) ↦ page θ u` maps `[0, 1) × (open disk)` bijectively onto `S \ x(ℝ)`, with
   injective differential (so `θ` is a smooth fibration `S \ x(ℝ) → ℝ/ℤ`). -/
structure AdaptedDiskOpenBook (H : R4 → ℝ) (P : PeriodicOrbit H) where
  page : ℝ → Plane → R4
  smooth : ContDiff ℝ ∞ (fun z : ℝ × Plane => page z.1 z.2)
  periodic : ∀ θ u, page (θ + 1) u = page θ u
  page_section : ∀ θ, IsDiskLikeGlobalSectionMap H P (page θ)
  binding : ∀ θ t, page θ (circlePoint t) = P.x (P.T * t)
  page_positive : ∀ θ, ∀ u ∈ openUnitDisk,
    0 < omega0 (fderiv ℝ (page θ) u (Pi.single 0 1)) (fderiv ℝ (page θ) u (Pi.single 1 1))
  fibration : ∀ y ∈ energySurface H, y ∉ P.image →
    ∃! z : ℝ × Plane, z.1 ∈ Set.Ico (0 : ℝ) 1 ∧ z.2 ∈ openUnitDisk ∧ page z.1 z.2 = y
  regular : ∀ θ : ℝ, ∀ u ∈ openUnitDisk,
    Function.Injective (fderiv ℝ (fun z : ℝ × Plane => page z.1 z.2) (θ, u))

/-- `P` is the binding of an adapted open book decomposition with disk-like pages. -/
def HasAdaptedDiskOpenBook (H : R4 → ℝ) (P : PeriodicOrbit H) : Prop :=
  Nonempty (AdaptedDiskOpenBook H P)

end

end HryniewiczCriterion


