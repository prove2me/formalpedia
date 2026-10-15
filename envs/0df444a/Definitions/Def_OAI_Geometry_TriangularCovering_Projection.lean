-- Prove2me | Definitions.Def_OAI_Geometry_TriangularCovering_Projection
-- name    : OAI_Geometry_TriangularCovering_Projection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T18:36:55.741553+00:00
-- url     : https://prove2.me/theorems/60d9fdc0-0149-43ae-aa99-4b377df53be7
-- title:
--   Orthogonal projection along a unit vector, projected triangle areas and projected triangular cylinders
-- statement:
--   Work in $\mathbb{R}^3$ with the standard inner product $\langle a,b\rangle=a_1b_1+a_2b_2+a_3b_3$. For a unit vector $u$ let $P_uz=z-\langle u,z\rangle u$ be the orthogonal projection onto the plane $u^\perp$, and write $\triangle(a,b,c)$ for the closed triangle with vertices $a,b,c$ and $G(b,c)=\langle b,b\rangle\langle c,c\rangle-\langle b,c\rangle^2$ for the Gram determinant. Recall that a *triangular cylinder* consists of a unit axis $u$ and a base which is a nondegenerate closed triangle contained in $u^\perp$ (with compactness, convexity, measurability and finite area recorded); its carrier is the set of points $p+ru$ with $p$ in the base and $r\in\mathbb{R}$.
--
--   1. **Projection as a linear map.** $P_u$ is linear, and for $\|u\|=1$ one has $\langle u,P_uz\rangle=0$ and $\langle P_ub,P_uc\rangle=\langle b,c\rangle-\langle u,b\rangle\langle u,c\rangle$.
--   2. **Cross product.** $b\times c=(b_2c_3-b_3c_2,\ b_3c_1-b_1c_3,\ b_1c_2-b_2c_1)$. Included identities: $\|b\times c\|^2=G(b,c)$, and for $\|u\|=1$, $G(P_ub,P_uc)=\langle u,b\times c\rangle^2$.
--   3. **Area of a projected triangle.** For $\|u\|=1$ and $a,b,c\in\mathbb{R}^3$,
--   $$
--   \mathcal H^2\big(P_u(\triangle(a,b,c))\big)=\frac{|\langle u,(b-a)\times(c-a)\rangle|}{2},
--   $$
--   where $\mathcal H^2$ is two-dimensional Hausdorff measure. Moreover $(b-a)\times(c-a)\neq0$ implies that $a,b,c$ are affinely independent, and $\langle u,(b-a)\times(c-a)\rangle\neq0$ implies that $P_ua,P_ub,P_uc$ are affinely independent. Triangles are compact.
--   4. **Projected cylinder.** Given a unit vector $u$ and points $a,b,c$ with $\langle u,(b-a)\times(c-a)\rangle\neq0$, the triangular cylinder $\mathcal C_u(a,b,c)$ has axis $u$ and base $P_u(\triangle(a,b,c))$, a nondegenerate triangle in $u^\perp$. Since $P_up+\langle u,p\rangle u=p$, its carrier is $\triangle(a,b,c)+\mathbb{R}u$.
--   5. **Normalization.** $\mathrm{unit}(v)=v/\|v\|$, which has norm $1$ for $v\neq0$.
--
--   Item 4 is how every cylinder of the covering of the tetrahedron is built: one chooses a triangle $\triangle(a,b,c)$ in a convenient coordinate plane and a tilted axis $u$, and item 3 gives the base area in closed form.
--
--   **Formalization Note** The Lean names are `projLinear`, `cross3`, `projection_triangle_measure`, `projectedCylinder` and `unit`; the projection itself (`projection`) and the structure `TriCylinder` come from the base definitions. In Lean $\mathrm{unit}(0)=0$ because $\|0\|^{-1}=0$. The nondegeneracy hypothesis is an argument of `projectedCylinder`, and all structure fields (perpendicularity, triangularity, compactness, convexity, measurability, finite area) are discharged inside the definition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/TriangularCovering/Projection.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/TriangularCovering/Projection.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangularCovering mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover
import Definitions.Def_OAI_Geometry_TriangularCovering_TriangleArea

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

def projLinear (u : Space) : Space →ₗ[ℝ] Space :=
  LinearMap.id - (innerₛₗ ℝ u).smulRight u

@[simp] lemma projLinear_apply (u z : Space) : projLinear u z = projection u z := rfl

lemma projection_perp {u : Space} (hu : ‖u‖ = 1) (z : Space) :
    inner ℝ u (projection u z) = 0 := by
  simp [projection, inner_sub_right, inner_smul_right, hu]

lemma projection_inner {u : Space} (hu : ‖u‖ = 1) (b c : Space) :
    inner ℝ (projection u b) (projection u c) =
      inner ℝ b c - inner ℝ u b * inner ℝ u c := by
  simp only [projection, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, conj_trivial, real_inner_self_eq_norm_sq, hu]
  rw [real_inner_comm b u]
  ring

def cross3 (b c : Space) : Space := WithLp.toLp 2 (crossProduct b.ofLp c.ofLp)

lemma inner_coord (a b : Space) :
    inner ℝ a b = a 0*b 0 + a 1*b 1 + a 2*b 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  ring

lemma cross3_coord (b c : Space) :
    cross3 b c = !₂[b 1*c 2-b 2*c 1, b 2*c 0-b 0*c 2, b 0*c 1-b 1*c 0] := rfl

lemma triple_gram_identity (u b c : Space) :
    (inner ℝ u (cross3 b c))^2 =
      inner ℝ u u * (inner ℝ b b * inner ℝ c c - (inner ℝ b c)^2) -
      inner ℝ b b * (inner ℝ u c)^2 - inner ℝ c c * (inner ℝ u b)^2 +
      2 * inner ℝ b c * inner ℝ u b * inner ℝ u c := by
  simp only [inner_coord, cross3_coord]
  dsimp
  ring

lemma projected_gram {u : Space} (hu : ‖u‖ = 1) (b c : Space) :
    inner ℝ (projection u b) (projection u b) * inner ℝ (projection u c) (projection u c) -
      (inner ℝ (projection u b) (projection u c))^2 = (inner ℝ u (cross3 b c))^2 := by
  rw [projection_inner hu, projection_inner hu, projection_inner hu, triple_gram_identity,
    real_inner_self_eq_norm_sq u, hu]
  ring

lemma projection_triangle_measure {u : Space} (hu : ‖u‖ = 1) (a b c : Space) :
    Measure.euclideanHausdorffMeasure 2 (projection u '' triangle a b c) =
      ENNReal.ofReal (|inner ℝ u (cross3 (b-a) (c-a))|/2) := by
  change Measure.euclideanHausdorffMeasure 2 (projLinear u '' triangle a b c) = _
  rw [triangle_image_linear]
  have hun : u ≠ 0 := by intro h; simp [h] at hu
  have hp := perpendicular_triangle_measure (E := Space) (by simp) u
    (projection u a) (projection u b) (projection u c) hun
    (projection_perp hu a) (projection_perp hu b) (projection_perp hu c)
  change Measure.euclideanHausdorffMeasure 2
    (triangle (projection u a) (projection u b) (projection u c)) = _
  rw [hp]
  have hab : projection u b - projection u a = projection u (b-a) :=
    ((projLinear u).map_sub b a).symm
  have hac : projection u c - projection u a = projection u (c-a) :=
    ((projLinear u).map_sub c a).symm
  rw [hab, hac, projected_gram hu, Real.sqrt_sq_eq_abs]

lemma cross3_gram (b c : Space) :
    inner ℝ (cross3 b c) (cross3 b c) =
      inner ℝ b b * inner ℝ c c - (inner ℝ b c)^2 := by
  simp only [inner_coord, cross3_coord]
  dsimp
  ring

lemma affineIndependent_of_cross3_ne_zero (a b c : Space)
    (h : cross3 (b-a) (c-a) ≠ 0) : AffineIndependent ℝ (![a,b,c] : Fin 3 → Space) := by
  have hpi : crossProduct (b-a).ofLp (c-a).ofLp ≠ 0 := by
    intro hz
    apply h
    unfold cross3
    rw [hz]
    rfl
  have hl := crossProduct_ne_zero_iff_linearIndependent.mp hpi
  have hlE : LinearIndependent ℝ (![b-a,c-a] : Fin 2 → Space) := by
    apply LinearIndependent.of_comp (EuclideanSpace.equiv (Fin 3) ℝ).toLinearMap
    convert hl using 1
    funext i
    fin_cases i <;> rfl
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ 0,
    ← linearIndependent_equiv (finSuccAboveEquiv (0 : Fin 3))]
  convert hlE using 1
  · ext i
    fin_cases i <;> rfl
  · rfl

lemma projected_affineIndependent {u : Space} (hu : ‖u‖ = 1) (a b c : Space)
    (h : inner ℝ u (cross3 (b-a) (c-a)) ≠ 0) :
    AffineIndependent ℝ (![projection u a, projection u b, projection u c] : Fin 3 → Space) := by
  apply affineIndependent_of_cross3_ne_zero
  have hab : projection u b - projection u a = projection u (b-a) :=
    ((projLinear u).map_sub b a).symm
  have hac : projection u c - projection u a = projection u (c-a) :=
    ((projLinear u).map_sub c a).symm
  rw [hab, hac]
  intro hz
  have hh := cross3_gram (projection u (b-a)) (projection u (c-a))
  rw [hz, inner_zero_left, projected_gram hu] at hh
  exact h (sq_eq_zero_iff.mp hh.symm)

lemma triangle_compact (a b c : Space) : IsCompact (triangle a b c) :=
  (finite_range (![a,b,c] : Fin 3 → Space)).isCompact_convexHull ℝ

def projectedCylinder (u : Space) (hu : ‖u‖ = 1) (a b c : Space)
    (h : inner ℝ u (cross3 (b-a) (c-a)) ≠ 0) : TriCylinder where
  axis := u
  base := projection u '' triangle a b c
  unit_axis := hu
  perpendicular := by
    rintro _ ⟨z, _, rfl⟩
    exact projection_perp hu z
  triangular := by
    refine ⟨![projection u a, projection u b, projection u c],
      projected_affineIndependent hu a b c h, ?_⟩
    exact triangle_image_linear (projLinear u) a b c
  compact := (triangle_compact a b c).image (projLinear u).continuous_of_finiteDimensional
  convex := (convex_convexHull ℝ _).linear_image (projLinear u)
  measurable := ((triangle_compact a b c).image
    (projLinear u).continuous_of_finiteDimensional).measurableSet
  finite_area := by rw [projection_triangle_measure hu]; exact ENNReal.ofReal_ne_top

def unit (v : Space) : Space := ‖v‖⁻¹ • v

lemma unit_norm {v : Space} (hv : v ≠ 0) : ‖unit v‖ = 1 := by
  simp [unit, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

end TriangularCovering

end

end OAI


